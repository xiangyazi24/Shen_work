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
      p ha hb u₀ hu₀.toPositive with
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
      p ha hb u₀ hu₀.toPositive with
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
      p ha hb u₀ hu₀.toPositive with
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
      p ha hb u₀ hu₀.toPositive with
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
      p ha hb u₀ hu₀.toPositive with
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

/-- Theorem 2.1 part 1 for the unit-point domain in the `0 < a ∧ 0 < b`
regime.  Any `PositiveGlobalBoundedSolution` on unitPointDomain satisfies
the ODE `f'(t) = f(t)(a − b f(t)^α)`.  The inverse-power substitution
`h(t) = f(t)^(−α)` reduces to the linear ODE `h' = −αa h + αb`, whose
solutions satisfy `h(t) ≤ max(h(1), b/a)` for `t ≥ 1`.  Since
`f(t) = h(t)^(−1/α)` is decreasing in `h`, we get
`f(t) ≥ min(f(1), (a/b)^(1/α))` for all `t ≥ 1`. -/
theorem unitPointDomain.Theorem_2_1_part1_when_a_pos_b_pos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    Theorem_2_1_part1 ShenWork.Paper2.unitPointDomain p := by
  intro _hm u v hsol
  obtain ⟨hglobal, _hbdd, hupos⟩ := hsol
  -- Setup: f(t) = u t (), e = (a/b)^(1/α)
  set f : ℝ → ℝ := fun t => u t () with hf_def
  set e : ℝ := (p.a / p.b) ^ (1 / p.α) with he_def
  -- f is differentiable
  have hf_diff : Differentiable ℝ f := by
    have h := hglobal.regularity (T := 1) (by norm_num : (0 : ℝ) < 1)
    exact h.1
  -- f(t) > 0 for t > 0
  have hf_pos : ∀ t, 0 < t → 0 < f t := by
    intro t ht
    exact hupos t () ht (Set.mem_univ _)
  -- PDE: deriv f t = f t * (a - b * (f t)^α) for all t > 0
  have hpde : ∀ t, 0 < t →
      deriv f t = f t * (p.a - p.b * (f t) ^ p.α) := by
    intro t ht
    have h := hglobal.pde_u (t := t) ht (Set.mem_univ ())
    simpa [ShenWork.Paper2.unitPointDomain] using h
  -- Key constants
  have hα_pos : 0 < p.α := p.hα
  have hα_ne : p.α ≠ 0 := ne_of_gt hα_pos
  have he_pos : 0 < e := Real.rpow_pos_of_pos (div_pos ha hb) _
  -- f(1) > 0
  have hf1_pos : 0 < f 1 := hf_pos 1 one_pos
  -- v t () = (ν/μ) * (f t)^γ for t > 0
  have hv_eq : ∀ t, 0 < t → v t () = (p.ν / p.μ) * (f t) ^ p.γ := by
    intro t ht
    have h := hglobal.pde_v (t := t) ht (Set.mem_univ ())
    simp only [ShenWork.Paper2.unitPointDomain] at h
    have hμ_ne : p.μ ≠ 0 := ne_of_gt p.hμ
    field_simp at h ⊢
    linarith
  -- === Inverse-power substitution ===
  -- Define g(t) = f(t)^(-α) for t > 0.  We'll show g satisfies a linear ODE.
  -- HasDerivAt for g: g'(t) = -αa g(t) + αb  for t > 0
  have hg_linear_ode : ∀ t, 0 < t →
      HasDerivAt (fun s => (f s) ^ (-p.α))
        (-(p.α * p.a) * (f t) ^ (-p.α) + p.α * p.b) t := by
    intro t ht
    have hf_ne : f t ≠ 0 := ne_of_gt (hf_pos t ht)
    -- Raw derivative from chain rule
    have hraw := (hf_diff t).hasDerivAt.rpow_const (Or.inl hf_ne) (p := -p.α)
    -- hraw : HasDerivAt (fun y => f y ^ (-α)) (deriv f t * (-α) * f(t)^(-α-1)) t
    -- Substitute deriv f t = f(t) * (a - b * f(t)^α) and simplify
    have hpow_cancel : (f t) ^ (-p.α) * (f t) ^ p.α = 1 := by
      rw [← Real.rpow_add (hf_pos t ht)]
      simp [Real.rpow_zero]
    have hpow_combine : (f t) * (f t) ^ (-p.α - 1) = (f t) ^ (-p.α) := by
      have h2 := Real.rpow_add (hf_pos t ht) 1 (-p.α - 1)
      rw [Real.rpow_one, show (1 : ℝ) + (-p.α - 1) = -p.α from by ring] at h2
      exact h2.symm
    convert hraw using 1
    rw [hpde t ht]
    -- Need: -(αa) * g + αb = f * (a - b*f^α) * (-α) * f^(-α-1)
    -- RHS = (-α) * (f * f^(-α-1)) * (a - b*f^α) = (-α) * f^(-α) * (a - b*f^α)
    -- = -α*a*f^(-α) + α*b*f^(-α)*f^α = -α*a*g + α*b*1 = -αa*g + αb
    have hstep : f t * (p.a - p.b * (f t) ^ p.α) * (-p.α) * (f t) ^ (-p.α - 1) =
        (-p.α) * (f t) ^ (-p.α) * (p.a - p.b * (f t) ^ p.α) := by
      rw [← hpow_combine]; ring
    rw [hstep]
    have hexpand : (-p.α) * (f t) ^ (-p.α) * (p.a - p.b * (f t) ^ p.α) =
        -(p.α * p.a) * (f t) ^ (-p.α) + p.α * p.b * ((f t) ^ (-p.α) * (f t) ^ p.α) := by
      ring
    rw [hexpand, hpow_cancel]; ring
  -- Define the integrating factor: ψ(t) = (g(t) - b/a) * exp(αa*t)
  set rate : ℝ := p.α * p.a with hrate_def
  have hrate_pos : 0 < rate := mul_pos hα_pos ha
  have ha_ne : p.a ≠ 0 := ne_of_gt ha
  -- Show ψ'(t) = 0 for t > 0, hence ψ is constant on (0,∞)
  have hpsi_deriv_zero : ∀ s ∈ Set.Ioi (0 : ℝ),
      deriv (fun t => ((f t) ^ (-p.α) - p.b / p.a) * Real.exp (rate * t)) s = 0 := by
    intro s hs
    have hs_pos : 0 < s := hs
    -- HasDerivAt for the two factors
    have hg_hd := hg_linear_ode s hs_pos
    have hconst_hd : HasDerivAt (fun _ : ℝ => p.b / p.a) 0 s := hasDerivAt_const s _
    have hsub_hd := hg_hd.sub hconst_hd
    -- hsub_hd : HasDerivAt (fun t => f(t)^(-α) - b/a) (-rate * f(s)^(-α) + αb - 0) s
    have hexp_hd : HasDerivAt (fun t => Real.exp (rate * t))
        (rate * Real.exp (rate * s)) s := by
      have := ((hasDerivAt_id s).const_mul rate).exp
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hsub_hd' : HasDerivAt (fun t => (f t) ^ (-p.α) - p.b / p.a)
        (-(rate) * (f s) ^ (-p.α) + p.α * p.b) s := by
      convert hsub_hd using 1; ring
    have hprod := hsub_hd'.mul hexp_hd
    have hfun_eq : (fun t => (f t) ^ (-p.α) - p.b / p.a) * (fun t => Real.exp (rate * t)) =
        fun t => ((f t) ^ (-p.α) - p.b / p.a) * Real.exp (rate * t) := rfl
    rw [show deriv (fun t => ((f t) ^ (-p.α) - p.b / p.a) * Real.exp (rate * t)) s =
        deriv ((fun t => (f t) ^ (-p.α) - p.b / p.a) * (fun t => Real.exp (rate * t))) s from rfl]
    rw [hprod.deriv]
    rw [hrate_def]; field_simp; ring
  -- ψ is differentiable on (0, ∞)
  have hpsi_diffOn :
      DifferentiableOn ℝ
        (fun t => ((f t) ^ (-p.α) - p.b / p.a) * Real.exp (rate * t))
        (Set.Ioi 0) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have hg_da := (hg_linear_ode t ht_pos).sub (hasDerivAt_const t (p.b / p.a))
    have hexp_da : HasDerivAt (fun s => Real.exp (rate * s))
        (rate * Real.exp (rate * t)) t := by
      have := ((hasDerivAt_id t).const_mul rate).exp
      simpa [mul_comm, mul_assoc] using this
    exact (hg_da.mul hexp_da).differentiableAt.differentiableWithinAt
  -- ψ is constant on (0, ∞): use is_const_of_deriv_eq_zero
  have hpsi_const : ∀ t₁, 0 < t₁ → ∀ t₂, 0 < t₂ →
      ((f t₁) ^ (-p.α) - p.b / p.a) * Real.exp (rate * t₁) =
      ((f t₂) ^ (-p.α) - p.b / p.a) * Real.exp (rate * t₂) := by
    intro t₁ ht₁ t₂ ht₂
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      hpsi_diffOn hpsi_deriv_zero ht₁ ht₂
  -- Specialize: ψ(t) = ψ(1) for all t > 0
  have hpsi_eq : ∀ t, 0 < t →
      ((f t) ^ (-p.α) - p.b / p.a) * Real.exp (rate * t) =
      ((f 1) ^ (-p.α) - p.b / p.a) * Real.exp (rate * 1) :=
    fun t ht => hpsi_const t ht 1 one_pos
  -- Therefore: f(t)^(-α) = b/a + (f(1)^(-α) - b/a) * exp(-rate*(t-1))
  have hg_formula : ∀ t, 0 < t →
      (f t) ^ (-p.α) = p.b / p.a +
        ((f 1) ^ (-p.α) - p.b / p.a) * Real.exp (-rate * (t - 1)) := by
    intro t ht
    have hexp_pos : 0 < Real.exp (rate * t) := Real.exp_pos _
    have hexp_ne : Real.exp (rate * t) ≠ 0 := ne_of_gt hexp_pos
    have h := hpsi_eq t ht
    -- (g(t) - b/a) * exp(rate*t) = (g(1) - b/a) * exp(rate)
    -- g(t) - b/a = (g(1) - b/a) * exp(rate) * exp(-rate*t)
    -- g(t) = b/a + (g(1) - b/a) * exp(rate - rate*t)
    -- g(t) = b/a + (g(1) - b/a) * exp(-rate*(t-1))
    rw [mul_comm ((f t) ^ (-p.α) - p.b / p.a) _, mul_comm ((f 1) ^ (-p.α) - p.b / p.a) _] at h
    have hdiv : (f t) ^ (-p.α) - p.b / p.a =
        ((f 1) ^ (-p.α) - p.b / p.a) * (Real.exp (rate * 1) / Real.exp (rate * t)) := by
      field_simp at h ⊢
      linarith
    rw [show Real.exp (rate * 1) / Real.exp (rate * t) = Real.exp (-rate * (t - 1)) by
      rw [← Real.exp_sub]
      congr 1; ring] at hdiv
    linarith
  -- Upper bound on g(t) for t ≥ 1:  g(t) ≤ max(g(1), b/a)
  have hg_upper : ∀ t, 1 ≤ t →
      (f t) ^ (-p.α) ≤ max ((f 1) ^ (-p.α)) (p.b / p.a) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht
    rw [hg_formula t ht_pos]
    -- g(t) = b/a + (g(1) - b/a) * exp(-rate*(t-1))
    -- For t ≥ 1: exp(-rate*(t-1)) ∈ [0, 1] (since rate > 0 and t-1 ≥ 0)
    have hexp_le_one : Real.exp (-rate * (t - 1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    have hexp_nn : 0 ≤ Real.exp (-rate * (t - 1)) := (Real.exp_pos _).le
    by_cases hcase : (f 1) ^ (-p.α) ≤ p.b / p.a
    · -- g(1) ≤ b/a: coefficient ≤ 0, so convex combination ≤ b/a
      have hcoef : (f 1) ^ (-p.α) - p.b / p.a ≤ 0 := by linarith
      calc p.b / p.a + ((f 1) ^ (-p.α) - p.b / p.a) * Real.exp (-rate * (t - 1))
          ≤ p.b / p.a + 0 := by nlinarith
        _ = p.b / p.a := by ring
        _ ≤ max ((f 1) ^ (-p.α)) (p.b / p.a) := le_max_right _ _
    · -- g(1) > b/a: coefficient > 0, exp ≤ 1, so g(t) ≤ g(1)
      push Not at hcase
      have hcoef : 0 < (f 1) ^ (-p.α) - p.b / p.a := by linarith
      calc p.b / p.a + ((f 1) ^ (-p.α) - p.b / p.a) * Real.exp (-rate * (t - 1))
          ≤ p.b / p.a + ((f 1) ^ (-p.α) - p.b / p.a) * 1 := by nlinarith
        _ = (f 1) ^ (-p.α) := by ring
        _ ≤ max ((f 1) ^ (-p.α)) (p.b / p.a) := le_max_left _ _
  -- Lower bound on f(t): f(t) ≥ min(f(1), e) for t ≥ 1
  -- Since f(t) = g(t)^(-1/α) and g ↦ g^(-1/α) is anti-monotone for g > 0,
  -- g(t) ≤ max(g(1), b/a) ⟹ f(t) ≥ min(f(1), e)
  have hf_lower : ∀ t, 1 ≤ t → min (f 1) e ≤ f t := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht
    have hft_pos : 0 < f t := hf_pos t ht_pos
    have hg1_pos : 0 < (f 1) ^ (-p.α) := Real.rpow_pos_of_pos hf1_pos _
    have hgt_pos : 0 < (f t) ^ (-p.α) := Real.rpow_pos_of_pos hft_pos _
    have hq_pos : 0 < p.b / p.a := div_pos hb ha
    -- f(t) = g(t)^(-1/α), f(1) = g(1)^(-1/α)
    have hf_recover : ∀ s, 0 < f s → f s = ((f s) ^ (-p.α)) ^ (-1 / p.α) := by
      intro s hs
      rw [← Real.rpow_mul hs.le]
      have : (-p.α) * (-1 / p.α) = 1 := by field_simp [hα_ne]
      rw [this, Real.rpow_one]
    -- e = (b/a)^(-1/α)
    have he_recover : e = (p.b / p.a) ^ (-1 / p.α) := by
      rw [he_def, show -1 / p.α = -(1 / p.α) by ring]
      rw [Real.rpow_neg_eq_inv_rpow]
      congr 1
      field_simp [ne_of_gt ha, ne_of_gt hb]
    -- -1/α < 0
    have hneg_inv : -1 / p.α < 0 := div_neg_of_neg_of_pos (by norm_num) hα_pos
    have hneg_inv_le : -1 / p.α ≤ 0 := hneg_inv.le
    -- Anti-monotonicity: if g(t) ≤ max(g(1), b/a), then
    -- f(t) = g(t)^(-1/α) ≥ max(g(1), b/a)^(-1/α) = min(g(1)^(-1/α), (b/a)^(-1/α))
    --      = min(f(1), e)
    have hgupper := hg_upper t ht
    -- max(g(1), b/a) > 0
    have hmax_pos : 0 < max ((f 1) ^ (-p.α)) (p.b / p.a) :=
      lt_max_of_lt_left hg1_pos
    -- rpow is antitone for negative exponent on positives
    have hanti := Real.rpow_le_rpow_of_nonpos hgt_pos hgupper hneg_inv_le
    rw [hf_recover t hft_pos]
    -- Need: max(g1, b/a)^(-1/α) ≤ f(t)^(-α)^(-1/α), and
    -- max(g1, b/a)^(-1/α) = min(g1^(-1/α), (b/a)^(-1/α)) = min(f1, e)
    suffices hsuff :
        min (f 1) e ≤ (max ((f 1) ^ (-p.α)) (p.b / p.a)) ^ (-1 / p.α) from
      le_trans hsuff hanti
    -- Case split on which is the max
    rcases le_or_gt ((f 1) ^ (-p.α)) (p.b / p.a) with hle | hgt_case
    · -- g(1) ≤ b/a, so max = b/a, and max^(-1/α) = e
      rw [max_eq_right hle, ← he_recover]
      exact min_le_right _ _
    · -- g(1) > b/a, so max = g(1), and max^(-1/α) = f(1)
      rw [max_eq_left hgt_case.le, ← hf_recover 1 hf1_pos]
      exact min_le_left _ _
  -- Set δu = min(f(1), e)
  have hδ_pos : 0 < min (f 1) e := lt_min hf1_pos he_pos
  refine ⟨min (f 1) e, hδ_pos, ?_, ?_⟩
  · -- EventuallyLowerBound D u (min (f 1) e)
    refine ⟨hδ_pos, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨1, fun t ht => ?_⟩
    exact hf_lower t ht
  · -- EventuallyLowerBound D v (ν/μ * (min (f 1) e)^γ)
    have hv_lb_pos : 0 < p.ν / p.μ * (min (f 1) e) ^ p.γ :=
      mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hδ_pos _)
    refine ⟨hv_lb_pos, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨1, fun t ht => ?_⟩
    have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht
    change p.ν / p.μ * (min (f 1) e) ^ p.γ ≤
      ShenWork.Paper2.unitPointDomain.infValue (v t)
    change p.ν / p.μ * (min (f 1) e) ^ p.γ ≤ v t ()
    rw [hv_eq t ht_pos]
    apply mul_le_mul_of_nonneg_left _ (div_pos p.hν p.hμ).le
    exact Real.rpow_le_rpow hδ_pos.le (hf_lower t ht) p.hγ.le

/-! ### Theorem_2_1 FULL composites using part1_when_a_pos_b_pos -/

/-- Paper 3 Theorem 2.1 full composite when `0 < p.a, 0 < p.b, p.χ₀ ≤ 0`.
**Broadest** a>0,b>0 composite: part 1 fires via the logistic ODE argument
(no m restriction); parts 2–3 vacuous via `chi_nonpos`;
part 4 vacuous via `a_nonzero`.
Strictly stronger than `Theorem_2_1_vacuous_when_a_pos_b_pos_chi_nonpos_m_lt_one`
(drops the `p.m < 1` hypothesis). -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_b_pos_chi_nonpos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (hχ : p.χ₀ ≤ 0)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos_b_pos p ha hb,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- Paper 3 Theorem 2.1 full composite when `0 < p.a, 0 < p.b, p.β < 1`.
Part 1 fires via the logistic ODE argument (no m restriction);
parts 2–3 vacuous via `beta_lt_one`; part 4 vacuous via `a_nonzero`. -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_b_pos_beta_lt_one
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (hβ : p.β < 1)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos_b_pos p ha hb,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_beta_lt_one p hβ,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_beta_lt_one p hβ,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- Paper 3 Theorem 2.1 full composite when
`0 < p.a, 0 < p.b, p.m ≤ 1, p.χ₀ ≤ 0`.
Part 1 fires via the logistic ODE argument;
part 2 vacuous via `chi_nonpos`; part 3 vacuous via `m_le_one`;
part 4 vacuous via `a_nonzero`. -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_b_pos_m_le_one_chi_nonpos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (hm : p.m ≤ 1)
    (hχ : p.χ₀ ≤ 0)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos_b_pos p ha hb,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_m_le_one p hm,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- Paper 3 Theorem 2.1 full composite when
`0 < p.a, 0 < p.b, p.m ≠ 1, p.χ₀ ≤ 0`.
Part 1 fires via the logistic ODE argument;
part 2 vacuous via `m_ne_one`; part 3 vacuous via `chi_nonpos`;
part 4 vacuous via `a_nonzero`. -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_b_pos_m_ne_one_chi_nonpos
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (hm : p.m ≠ 1)
    (hχ : p.χ₀ ≤ 0)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos_b_pos p ha hb,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_m_ne_one p hm,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- On unitPointDomain with a > 0 and b = 0, no PositiveGlobalBoundedSolution
exists: the PDE forces u' = au with a > 0, giving exponential growth that
contradicts IsPaper2Bounded. Hence Theorem_2_1_part1 is vacuously true. -/
theorem unitPointDomain.Theorem_2_1_part1_when_a_pos_b_zero
    (p : CM2Params) (ha : 0 < p.a) (hb : p.b = 0) :
    Theorem_2_1_part1 ShenWork.Paper2.unitPointDomain p := by
  intro _hm u v hsol
  exfalso
  obtain ⟨hglobal, hbdd, hupos⟩ := hsol
  -- From IsPaper2Bounded: ∃ M, eventually |u t ()| ≤ M
  obtain ⟨M, hM⟩ := hbdd
  rw [Filter.eventually_atTop] at hM
  obtain ⟨T₀, hT₀⟩ := hM
  -- PDE: deriv (fun s => u s ()) t = u t () * a for all t > 0
  have hpde : ∀ t : ℝ, 0 < t →
      deriv (fun s : ℝ => u s ()) t = u t () * p.a := by
    intro t ht
    have hT := hglobal (t + 1) (by linarith)
    have h := hT.pde_u (t := t) (x := ()) ht (by linarith) (Set.mem_univ _)
    simp only [ShenWork.Paper2.unitPointDomain] at h
    rw [hb] at h; simp at h; linarith
  -- Differentiable
  have hdiff : Differentiable ℝ (fun t : ℝ => u t ()) :=
    (hglobal 2 (by norm_num : (0:ℝ) < 2)).regularity.1
  -- u(1)() > 0
  have hu1_pos : 0 < u 1 () := hupos 1 () one_pos (Set.mem_univ _)
  -- From PDE: u' = au > 0, so u is increasing on (0,∞)
  -- By monotoneOn_of_deriv_nonneg: u increasing on [1, ∞)
  -- u(t) ≥ u(1) for t ≥ 1, so deriv ≥ a·u(1) > 0
  -- Linear growth: u(t) ≥ u(1) + a·u(1)·(t-1) → ∞
  -- Eventually exceeds M, contradicting bounded
  have hderiv_pos : ∀ t : ℝ, 1 ≤ t → 0 ≤ deriv (fun s => u s ()) t := by
    intro t ht
    rw [hpde t (lt_of_lt_of_le one_pos ht)]
    exact mul_nonneg (le_of_lt (hupos t () (lt_of_lt_of_le one_pos ht) (Set.mem_univ _))) ha.le
  have hmono : MonotoneOn (fun t : ℝ => u t ()) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (hdiff.continuous.continuousOn)
      (fun t _ht => (hdiff t).differentiableWithinAt)
      (fun t ht => by rw [interior_Ici] at ht; exact hderiv_pos t (Set.mem_Ioi.mp ht).le)
  have hderiv_lb : ∀ t : ℝ, 1 ≤ t →
      p.a * u 1 () ≤ deriv (fun s => u s ()) t := by
    intro t ht
    rw [hpde t (lt_of_lt_of_le one_pos ht)]
    rw [mul_comm p.a (u 1 ())]
    exact mul_le_mul_of_nonneg_right
      (hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht) ha.le
  -- Use Convex.mul_sub_le_image_sub_of_le_deriv for linear lower bound
  set f : ℝ → ℝ := fun s => u s () with hf_def
  have hlinear : ∀ t : ℝ, 1 ≤ t →
      f 1 + p.a * f 1 * (t - 1) ≤ f t := by
    intro t ht
    have hcont_on : ContinuousOn f (Set.Ici 1) :=
      hdiff.continuous.continuousOn.mono (Set.Ici_subset_Ici.mpr le_rfl)
    have hdiff_on : DifferentiableOn ℝ f (interior (Set.Ici 1)) := by
      rw [interior_Ici]
      exact hdiff.differentiableOn.mono Set.Ioi_subset_Ici_self
    have hbound : ∀ x ∈ interior (Set.Ici (1 : ℝ)),
        p.a * f 1 ≤ deriv f x := by
      intro x hx; rw [interior_Ici] at hx
      exact hderiv_lb x (Set.mem_Ioi.mp hx).le
    have h := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici 1)
      hcont_on hdiff_on hbound
      1 (Set.mem_Ici.mpr le_rfl) t (Set.mem_Ici.mpr ht) ht
    linarith
  -- Choose t large enough to exceed M
  have hau_pos : 0 < p.a * u 1 () := mul_pos ha hu1_pos
  set t_star := max T₀ 1 + (|M| + 1) / (p.a * u 1 ()) + 1
  have hdiv_nonneg : 0 ≤ (|M| + 1) / (p.a * u 1 ()) :=
    div_nonneg (by linarith [abs_nonneg M]) hau_pos.le
  have ht_ge_1 : 1 ≤ t_star := by
    simp only [t_star]; linarith [le_max_right T₀ 1]
  have ht_ge_T₀ : T₀ ≤ t_star := by
    simp only [t_star]; linarith [le_max_left T₀ (1 : ℝ)]
  have hu_large : |M| + 1 < u t_star () - u 1 () := by
    have h := hlinear t_star ht_ge_1
    have ht_diff : t_star - 1 > (|M| + 1) / (p.a * u 1 ()) := by
      simp only [t_star]
      linarith [le_max_right T₀ 1]
    have := mul_lt_mul_of_pos_left ht_diff hau_pos
    rw [mul_div_cancel₀ _ (ne_of_gt hau_pos)] at this
    linarith
  have hu_exceeds : M < u t_star () := by
    have : u 1 () ≥ 0 := hu1_pos.le
    linarith [le_abs_self M]
  have hbdd_contra := hT₀ t_star ht_ge_T₀
  simp only [ShenWork.Paper2.unitPointDomain] at hbdd_contra
  linarith [le_abs_self (u t_star ())]

/-- Theorem 2.1 full composite for (a > 0, b = 0) — NO restriction on m, β, χ.
All parts are vacuous: parts 2-3 via b=0, part 4 via a≠0, part 1 via
nonexistence of PGBS (exponential growth). -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_b_zero
    (p : CM2Params) (ha : 0 < p.a) (hb : p.b = 0)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos_b_zero p ha hb,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_b_zero p hb,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_b_zero p hb,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- Theorem_2_1_part1 is **genuinely FALSE** for (a = 0, b > 0) on
unitPointDomain: the decay ODE u' = -bu^{α+1} drives every positive
solution to 0, so no positive eventual lower bound exists.

This shows the (a=0, b>0) gap in our part1 coverage is a REAL
mathematical limitation, not a proof gap. -/
theorem unitPointDomain.not_Theorem_2_1_part1_when_a_zero_b_pos :
    ∃ p : CM2Params, p.a = 0 ∧ 0 < p.b ∧ 1 ≤ p.m ∧
      ¬ Theorem_2_1_part1 ShenWork.Paper2.unitPointDomain p := by
  -- Counterexample params: a=0, b=1, α=1, m=1
  set p : CM2Params :=
    { N := 1, hN := by norm_num, α := 1, γ := 1, m := 1, μ := 1, ν := 1,
      χ₀ := 0, a := 0, b := 1, β := 1,
      hα := by norm_num, hγ := by norm_num, hm := by norm_num,
      hμ := by norm_num, hν := by norm_num,
      ha := by norm_num, hb := by norm_num, hβ := by norm_num } with hp_def
  refine ⟨p, rfl, by norm_num [p], le_refl _, ?_⟩
  -- Assume Theorem_2_1_part1 holds
  intro h21
  -- Build initial datum u₀ ≡ 1
  set u₀ : ShenWork.Paper2.unitPointDomain.Point → ℝ := fun _ => 1 with hu₀_def
  have hu₀_pid : ShenWork.Paper2.PositiveInitialDatum ShenWork.Paper2.unitPointDomain u₀ :=
    ⟨trivial, fun _ _ => by norm_num⟩
  -- Get decay ODE solution with bound
  have ha : p.a = 0 := rfl
  have hb : 0 < p.b := by norm_num [p]
  rcases ShenWork.Paper2.unitPointDecay_globalExistence_with_bound p ha hb u₀ hu₀_pid with
    ⟨u, v, hglobal, _htrace, hbound⟩
  -- Build PositiveGlobalBoundedSolution
  have hbdd : ShenWork.Paper2.IsPaper2Bounded
      ShenWork.Paper2.unitPointDomain u :=
    ShenWork.Paper2.IsPaper2Bounded.of_forall_nonneg_supNorm_le
      (M := ShenWork.Paper2.unitPointDomain.supNorm u₀)
      (fun t ht => hbound t ht)
  have hpgbs : PositiveGlobalBoundedSolution
      ShenWork.Paper2.unitPointDomain p u v :=
    PositiveGlobalBoundedSolution.of_global_bounded hglobal hbdd
  -- Apply h21 to get δu > 0 with EventuallyLowerBound
  have hm : (1 : ℝ) ≤ p.m := le_refl _
  rcases h21 hm u v hpgbs with ⟨δu, hδu_pos, hδu_lower, _⟩
  -- EventuallyLowerBound says: 0 < δu ∧ ∀ᶠ t in atTop, δu ≤ infValue (u t)
  -- On unitPointDomain, infValue f = f ()
  rcases hδu_lower with ⟨_, hδu_ev⟩
  rw [Filter.eventually_atTop] at hδu_ev
  rcases hδu_ev with ⟨T₀, hT₀⟩
  -- The decay ODE u' = -u^{α+1} with α=1 gives u' = -u².
  -- Via 1/u trick: (1/u)' = 1, so 1/u(t) = 1/u(1) + (t-1).
  -- Hence u(t) → 0, contradicting the eventual lower bound.
  -- Extract differentiability, positivity, and the PDE u' = -u²
  have hdiff : Differentiable ℝ (fun s : ℝ => u s ()) := by
    have h2 := hglobal 2 (by norm_num : (0 : ℝ) < 2)
    exact h2.2.1.1
  have hupos : ∀ t : ℝ, 0 < t → 0 < u t () :=
    fun t ht => hglobal.u_pos ht (Set.mem_univ _)
  have hpde : ∀ t : ℝ, 0 < t →
      deriv (fun s : ℝ => u s ()) t = -(u t () ^ 2) := by
    intro t ht
    have h := hglobal.pde_u (t := t) ht (Set.mem_univ ())
    simp only [ShenWork.Paper2.unitPointDomain] at h
    have hpa : p.a = 0 := rfl
    have hpb : p.b = 1 := rfl
    have hpα : p.α = 1 := rfl
    rw [hpa, hpb, hpα, Real.rpow_one] at h
    linarith
  -- 1/u trick: g(t) := (u t ())⁻¹ satisfies g' = 1, so
  -- g(t) = g(1) + (t - 1), hence u(t) → 0 as t → ∞.
  have hg_deriv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => (u s ())⁻¹) 1 t := by
    intro t ht
    have hut_ne : u t () ≠ 0 := ne_of_gt (hupos t ht)
    have hut_sq_ne : u t () ^ 2 ≠ 0 := pow_ne_zero 2 hut_ne
    have hderiv_u : HasDerivAt (fun s => u s ()) (deriv (fun s => u s ()) t) t :=
      (hdiff t).hasDerivAt
    have hinv := hderiv_u.inv hut_ne
    convert hinv using 1
    rw [hpde t ht]
    rw [show -(-(u t () ^ 2)) = u t () ^ 2 by ring]
    rw [div_self hut_sq_ne]
  -- g - id has zero derivative on (0,∞), so is constant
  have hg_linear : ∀ t : ℝ, 0 < t →
      (u t ())⁻¹ = (u 1 ())⁻¹ + (t - 1) := by
    intro t ht
    have hg_minus_id_deriv : ∀ s ∈ Set.Ioi (0 : ℝ),
        deriv (fun r => (u r ())⁻¹ - r) s = 0 := by
      intro s hs
      have hsub_hd := (hg_deriv s hs).sub (hasDerivAt_id s)
      have : (fun r => (u r ())⁻¹ - r) =
          (fun s => (u s ())⁻¹) - id := by ext; simp
      rw [this, hsub_hd.deriv]
      ring
    have hg_minus_id_diff : DifferentiableOn ℝ (fun r => (u r ())⁻¹ - r) (Set.Ioi 0) := by
      intro s hs
      exact ((hg_deriv s hs).differentiableAt.sub differentiableAt_id).differentiableWithinAt
    have hconst := isOpen_Ioi.is_const_of_deriv_eq_zero
      isPreconnected_Ioi hg_minus_id_diff hg_minus_id_deriv
      (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr one_pos)
    linarith
  -- Choose t_star large enough so u(t_star) < δu
  have hu1_pos : 0 < u 1 () := hupos 1 one_pos
  have hu1_inv_pos : 0 < (u 1 ())⁻¹ := inv_pos.mpr hu1_pos
  -- Choose t_star large enough
  set t_star := max T₀ 1 + (u 1 ())⁻¹ + δu⁻¹ with ht_star_def
  have ht_star_pos : 0 < t_star := by
    simp only [t_star]
    linarith [le_max_right T₀ 1, inv_pos.mpr hδu_pos]
  have ht_star_ge_T₀ : T₀ ≤ t_star := by
    simp only [t_star]
    linarith [le_max_left T₀ (1 : ℝ), hu1_inv_pos, inv_pos.mpr hδu_pos]
  -- At t_star: (u 1 ())⁻¹ + (t_star - 1) > δu⁻¹
  have hden_large : δu⁻¹ < (u 1 ())⁻¹ + (t_star - 1) := by
    simp only [t_star]
    have : (1 : ℝ) ≤ max T₀ 1 := le_max_right T₀ 1
    linarith
  -- So u(t_star) = ((u 1 ())⁻¹ + (t_star - 1))⁻¹ < δu
  have hut_star_eq : (u t_star ())⁻¹ = (u 1 ())⁻¹ + (t_star - 1) :=
    hg_linear t_star ht_star_pos
  have hut_star_pos : 0 < u t_star () := hupos t_star ht_star_pos
  have hden_pos : 0 < (u 1 ())⁻¹ + (t_star - 1) := by linarith [inv_pos.mpr hδu_pos]
  have hut_star_val : u t_star () = ((u 1 ())⁻¹ + (t_star - 1))⁻¹ := by
    rw [← hut_star_eq, inv_inv]
  have hut_star_lt : u t_star () < δu := by
    rw [hut_star_val]
    exact (inv_lt_comm₀ hδu_pos hden_pos).mp hden_large
  -- But hT₀ says δu ≤ infValue (u t_star) = u t_star ()
  have hcontra := hT₀ t_star ht_star_ge_T₀
  -- infValue (u t) on unitPointDomain = u t ()
  change δu ≤ ShenWork.Paper2.unitPointDomain.infValue (u t_star) at hcontra
  change δu ≤ u t_star () at hcontra
  linarith

/-! ### Theorem_2_1 part1 covering ALL b when a > 0 -/

/-- Theorem 2.1 part 1 for the unit-point domain when `0 < p.a`,
covering ALL `b ≥ 0` by case-splitting:
- `b = 0`: vacuous (no PGBS exists -- exponential growth)
- `b > 0`: inverse-power substitution argument
This eliminates ALL restrictions on `b`, `m`, `β`, `χ` from part 1. -/
theorem unitPointDomain.Theorem_2_1_part1_when_a_pos
    (p : CM2Params) (ha : 0 < p.a) :
    Theorem_2_1_part1 ShenWork.Paper2.unitPointDomain p := by
  intro hm u v hsol
  by_cases hb : 0 < p.b
  · exact unitPointDomain.Theorem_2_1_part1_when_a_pos_b_pos p ha hb hm u v hsol
  · have hb0 : p.b = 0 := le_antisymm (not_lt.mp hb) p.hb
    exact unitPointDomain.Theorem_2_1_part1_when_a_pos_b_zero p ha hb0 hm u v hsol

/-! ### Theorem_2_1 full composites for a > 0 (all b) -/

/-- Paper 3 Theorem 2.1 full composite when `0 < p.a ∧ p.χ₀ ≤ 0`.
**Broadest** a > 0 composite: covers ALL `b ≥ 0` without any
restriction on `m` or `β`.
Part 1 fires via case split on b (b=0 vacuous, b>0 inverse-power);
parts 2-3 vacuous via `chi_nonpos`;
part 4 vacuous via `a_nonzero`.
Strictly generalises `Theorem_2_1_when_a_pos_b_pos_chi_nonpos`
(drops `0 < b`) and `Theorem_2_1_when_a_pos_b_zero` (adds chi condition
but keeps b unrestricted). -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_chi_nonpos
    (p : CM2Params) (ha : 0 < p.a) (hχ : p.χ₀ ≤ 0)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos p ha,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- Paper 3 Theorem 2.1 full composite when `0 < p.a ∧ p.β < 1`.
Covers ALL `b ≥ 0` without any restriction on `m` or `χ₀`.
Part 1 fires via case split on b; parts 2-3 vacuous via `beta_lt_one`;
part 4 vacuous via `a_nonzero`.
Strictly generalises `Theorem_2_1_when_a_pos_b_pos_beta_lt_one`
(drops `0 < b`). -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_beta_lt_one
    (p : CM2Params) (ha : 0 < p.a) (hβ : p.β < 1)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos p ha,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_beta_lt_one p hβ,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_beta_lt_one p hβ,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- Paper 3 Theorem 2.1 full composite when `0 < p.a ∧ p.m ≠ 1 ∧ p.χ₀ ≤ 0`.
Covers ALL `b ≥ 0` without any restriction on `β`.
Part 1 fires via case split on b; part 2 vacuous via `m_ne_one`;
part 3 vacuous via `chi_nonpos`; part 4 vacuous via `a_nonzero`.
Strictly generalises `Theorem_2_1_when_a_pos_b_pos_m_ne_one_chi_nonpos`
(drops `0 < b`). -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_m_ne_one_chi_nonpos
    (p : CM2Params) (ha : 0 < p.a) (hm : p.m ≠ 1) (hχ : p.χ₀ ≤ 0)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos p ha,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_m_ne_one p hm,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-- Paper 3 Theorem 2.1 full composite when `0 < p.a ∧ p.m ≤ 1 ∧ p.χ₀ ≤ 0`.
Covers ALL `b ≥ 0` without any restriction on `β`.
Part 1 fires via case split on b; part 2 vacuous via `chi_nonpos`;
part 3 vacuous via `m_le_one`; part 4 vacuous via `a_nonzero`.
Strictly generalises `Theorem_2_1_when_a_pos_b_pos_m_le_one_chi_nonpos`
(drops `0 < b`). -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_m_le_one_chi_nonpos
    (p : CM2Params) (ha : 0 < p.a) (hm : p.m ≤ 1) (hχ : p.χ₀ ≤ 0)
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  ⟨unitPointDomain.Theorem_2_1_part1_when_a_pos p ha,
    unitPointDomain.Theorem_2_1_part2_vacuous_when_chi_nonpos p hχ,
    unitPointDomain.Theorem_2_1_part3_vacuous_when_m_le_one p hm,
    unitPointDomain.Theorem_2_1_part4_vacuous_when_a_nonzero p (ne_of_gt ha) C⟩

/-! ### Instance-facing unit-point wrappers -/

/-- Instance-facing unit-point Proposition 1.2 in the logistic slice. -/
theorem unitPointDomain.Proposition_1_2_when_a_pos_b_posFact
    (p : CM2Params)
    [ha : Fact (0 < p.a)] [hb : Fact (0 < p.b)] :
    Proposition_1_2 ShenWork.Paper2.unitPointDomain p :=
  unitPointDomain.Proposition_1_2_when_a_pos_b_pos p ha.out hb.out

/-- Instance-facing unit-point Proposition 1.2 in the decay slice. -/
theorem unitPointDomain.Proposition_1_2_when_a_zero_b_posFact
    (p : CM2Params)
    [ha : Fact (p.a = 0)] [hb : Fact (0 < p.b)] :
    Proposition_1_2 ShenWork.Paper2.unitPointDomain p :=
  unitPointDomain.Proposition_1_2_when_a_zero_b_pos p ha.out hb.out

/-- Instance-facing unit-point Proposition 1.2 away from the exponential-growth
slice. -/
theorem unitPointDomain.Proposition_1_2_when_not_a_pos_b_zeroFact
    (p : CM2Params)
    [hnot : Fact (¬ (0 < p.a ∧ p.b = 0))] :
    Proposition_1_2 ShenWork.Paper2.unitPointDomain p :=
  unitPointDomain.Proposition_1_2_when_not_a_pos_b_zero p hnot.out

/-- Instance-facing unit-point Proposition 1.4 in the logistic slice. -/
theorem unitPointDomain.Proposition_1_4_when_a_pos_b_posFact
    (p : CM2Params)
    [ha : Fact (0 < p.a)] [hb : Fact (0 < p.b)] :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p :=
  unitPointDomain.Proposition_1_4_when_a_pos_b_pos p ha.out hb.out

/-- Instance-facing unit-point Proposition 1.4 in the decay slice. -/
theorem unitPointDomain.Proposition_1_4_when_a_zero_b_posFact
    (p : CM2Params)
    [ha : Fact (p.a = 0)] [hb : Fact (0 < p.b)] :
    Proposition_1_4 ShenWork.Paper2.unitPointDomain p :=
  unitPointDomain.Proposition_1_4_when_a_zero_b_pos p ha.out hb.out

/-- Instance-facing unit-point Theorem 2.1 in the
`0 < a ∧ χ₀ ≤ 0` slice. -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_chi_nonposFact
    (p : CM2Params)
    [ha : Fact (0 < p.a)] [hχ : Fact (p.χ₀ ≤ 0)]
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  unitPointDomain.Theorem_2_1_when_a_pos_chi_nonpos p ha.out hχ.out C

/-- Instance-facing unit-point Theorem 2.1 in the `0 < a ∧ β < 1` slice. -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_beta_lt_oneFact
    (p : CM2Params)
    [ha : Fact (0 < p.a)] [hβ : Fact (p.β < 1)]
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  unitPointDomain.Theorem_2_1_when_a_pos_beta_lt_one p ha.out hβ.out C

/-- Instance-facing unit-point Theorem 2.1 in the
`0 < a ∧ m ≠ 1 ∧ χ₀ ≤ 0` slice. -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_m_ne_one_chi_nonposFact
    (p : CM2Params)
    [ha : Fact (0 < p.a)] [hm : Fact (p.m ≠ 1)] [hχ : Fact (p.χ₀ ≤ 0)]
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  unitPointDomain.Theorem_2_1_when_a_pos_m_ne_one_chi_nonpos
    p ha.out hm.out hχ.out C

/-- Instance-facing unit-point Theorem 2.1 in the
`0 < a ∧ m ≤ 1 ∧ χ₀ ≤ 0` slice. -/
theorem unitPointDomain.Theorem_2_1_when_a_pos_m_le_one_chi_nonposFact
    (p : CM2Params)
    [ha : Fact (0 < p.a)] [hm : Fact (p.m ≤ 1)] [hχ : Fact (p.χ₀ ≤ 0)]
    (C : Paper3Constants ShenWork.Paper2.unitPointDomain p) :
    Theorem_2_1 ShenWork.Paper2.unitPointDomain p C :=
  unitPointDomain.Theorem_2_1_when_a_pos_m_le_one_chi_nonpos
    p ha.out hm.out hχ.out C

end ShenWork.Paper3

end
