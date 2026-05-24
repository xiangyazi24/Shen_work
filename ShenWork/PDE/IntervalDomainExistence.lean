/-
  ShenWork/PDE/IntervalDomainExistence.lean

  Local existence of classical solutions for the chemotaxis system
  on the unit interval [0,1].

  We construct the spatially-constant equilibrium solution:
    u(t,x) = c,   v(t,x) = (ν/μ)c^γ
  which is constant in both time and space.  For this to satisfy the PDE
  u_t = Δu - χ₀∇·(u∇v/(1+v)^β) + u(a - bu^α), the time derivative and
  all spatial derivatives must vanish, leaving c(a - bc^α) = 0.

  Two cases produce a positive constant c:
  - a = 0, b = 0: any c > 0 works (the reaction term vanishes).
  - a > 0, b > 0: the equilibrium c = (a/b)^{1/α} satisfies a - bc^α = 0.

  In both cases we verify every field of IsPaper2ClassicalSolution.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.ODEExistence

open ShenWork.Paper2 ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.IntervalDomainExistence

/-! ### Constant-in-space solutions on intervalDomain -/

/-- The elliptic relation v = (ν/μ)u^γ for constant-in-space functions. -/
def ellipticV (p : CM2Params) (φ : ℝ) : ℝ := (p.ν / p.μ) * φ ^ p.γ

lemma ellipticV_pos (p : CM2Params) {φ : ℝ} (hφ : 0 < φ) : 0 < ellipticV p φ :=
  mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hφ _)

/-- A spatially constant function on intervalDomainPoint. -/
def constOnInterval (c : ℝ) : intervalDomainPoint → ℝ := fun _ => c

lemma constOnInterval_pos {c : ℝ} (hc : 0 < c) :
    PositiveInitialDatum intervalDomain (constOnInterval c) := by
  constructor
  · trivial
  · intro x _hx; exact hc

/-! ### Lift of constant functions on intervalDomain -/

/-- The lift of a constant function on intervalDomainPoint equals
`c` on `[0,1]` and `0` outside. -/
lemma intervalDomainLift_const (c : ℝ) :
    intervalDomainLift (fun _ : intervalDomainPoint => c) =
      fun x => if x ∈ Set.Icc (0 : ℝ) 1 then c else 0 := by
  ext x
  simp [intervalDomainLift]

/-- At an interior point of (0,1), the lift of a constant function
agrees with the constant function `fun _ => c` in a neighborhood. -/
lemma intervalDomainLift_const_eventuallyEq (c : ℝ) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (fun y => if y ∈ Set.Icc (0 : ℝ) 1 then c else 0) =ᶠ[nhds x]
      fun _ => c := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.Ioo 0 1, Ioo_mem_nhds hx.1 hx.2, fun y hy => ?_⟩
  have hy' : y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
  simp [hy']

/-- The derivative of the lift of a constant function is zero at
any interior point of (0,1). -/
lemma intervalDomainLift_const_deriv_zero (c : ℝ) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) x = 0 := by
  rw [intervalDomainLift_const]
  have heq := intervalDomainLift_const_eventuallyEq c hx
  rw [Filter.EventuallyEq.deriv_eq heq]
  exact deriv_const x c

/-- The derivative function `fun y => deriv (lift (const c)) y`
is zero in a neighborhood of any interior point of (0,1). -/
lemma intervalDomainLift_const_deriv_eventuallyEq_zero (c : ℝ) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (fun y => deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) y)
      =ᶠ[nhds x] fun _ => 0 := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.Ioo 0 1, Ioo_mem_nhds hx.1 hx.2, fun y hy => ?_⟩
  exact intervalDomainLift_const_deriv_zero c hy

/-- The Laplacian of a constant function on intervalDomain is zero at
any interior point. -/
lemma intervalDomainLaplacian_const_zero (c : ℝ)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    intervalDomainLaplacian (fun _ : intervalDomainPoint => c) x = 0 := by
  unfold intervalDomainLaplacian
  have hx_ioo : (x.1 : ℝ) ∈ Set.Ioo 0 1 := hx
  have heq := intervalDomainLift_const_deriv_eventuallyEq_zero c hx_ioo
  rw [Filter.EventuallyEq.deriv_eq heq]
  exact deriv_const x.1 (0 : ℝ)

/-- The chemotaxis divergence term for constant functions is zero at
any interior point, since the spatial derivatives of constant lifts vanish. -/
lemma intervalDomainChemotaxisDiv_const_zero (p : CM2Params) (c₁ c₂ : ℝ)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    intervalDomainChemotaxisDiv p
      (fun _ : intervalDomainPoint => c₁)
      (fun _ : intervalDomainPoint => c₂) x = 0 := by
  unfold intervalDomainChemotaxisDiv
  have hx_ioo : (x.1 : ℝ) ∈ Set.Ioo 0 1 := hx
  have hv_deriv_zero : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      deriv (intervalDomainLift (fun _ : intervalDomainPoint => c₂)) y = 0 :=
    fun y hy => intervalDomainLift_const_deriv_zero c₂ hy
  have h_inner_zero : (fun y : ℝ =>
      intervalDomainLift (fun _ : intervalDomainPoint => c₁) y *
        deriv (intervalDomainLift (fun _ : intervalDomainPoint => c₂)) y /
        (1 + intervalDomainLift (fun _ : intervalDomainPoint => c₂) y) ^ p.β)
      =ᶠ[nhds x.1] fun _ => 0 := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo 0 1, Ioo_mem_nhds hx_ioo.1 hx_ioo.2, fun y hy => ?_⟩
    simp [hv_deriv_zero y hy]
  rw [Filter.EventuallyEq.deriv_eq h_inner_zero]
  exact deriv_const x.1 (0 : ℝ)

/-- The normal derivative of a constant function on intervalDomain is zero
at any boundary point. -/
lemma intervalDomainNormalDeriv_const_zero (c : ℝ)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.boundary) :
    intervalDomainNormalDeriv (fun _ : intervalDomainPoint => c) x = 0 :=
  intervalDomainNormalDeriv_endpoint _ hx

/-! ### Sup-norm of constant-in-space functions -/

/-- For a spatially constant function, the sup-norm equals the absolute value. -/
lemma intervalDomainSupNorm_const (φ : ℝ) :
    intervalDomainSupNorm (fun _ : intervalDomainPoint => φ) = |φ| := by
  unfold intervalDomainSupNorm
  have h : Set.range (fun _ : intervalDomainPoint => |φ|) = {|φ|} := by
    ext y
    simp only [Set.mem_range, exists_const_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · intro h
      have h01 : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
      exact ⟨⟨1 / 2, h01⟩, h.symm⟩
  rw [h, csSup_singleton]

/-! ### Classical regularity for constant-in-time-and-space solutions

For u(t,x) = c (constant in both time and space), the sup-norm is the
constant function `fun t => |c|`.  Its derivative is 0, which is trivially
nonpositive.  This verifies both conjuncts of `intervalDomainClassicalRegularity`
for any CM2Params. -/

/-- A constant-in-time-and-space solution satisfies the sup-norm regularity
condition because the sup-norm is constant with zero derivative. -/
lemma constantInTime_classicalRegularity
    {c : ℝ} (hc : 0 < c) {T : ℝ} (_hT : 0 < T) (p : CM2Params) :
    intervalDomainClassicalRegularity T
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c) := by
  unfold intervalDomainClassicalRegularity
  -- The sup-norm is constantly c.
  have hsup_eq : intervalDomainSupNorm (fun _ : intervalDomainPoint => c) = c := by
    rw [intervalDomainSupNorm_const, abs_of_pos hc]
  -- The sup-norm function is constant, hence continuous, differentiable,
  -- with zero derivative.
  have hsup_fun_eq :
      (fun t : ℝ => intervalDomainSupNorm
        ((fun _s (_ : intervalDomainPoint) => c) t)) = fun _ => c := by
    ext _; exact hsup_eq
  refine ⟨?_, ?_⟩
  · -- First conjunct: for any p' with a > 0, b > 0, if supNorm > equilibrium,
    -- the sup-norm is nonincreasing on Ioc 0 t₀.
    intro _p' _hχ _ha _hb t₀ _ht₀ _ht₀T _hsup_gt
    exact {
      continuousOn := by rw [hsup_fun_eq]; exact continuousOn_const
      differentiableOn := by rw [hsup_fun_eq]; exact differentiableOn_const c
      deriv_nonpos := by
        intro t _ht
        rw [hsup_fun_eq]; simp [deriv_const]
    }
  · -- Second conjunct: for any p' with a = 0, b = 0,
    -- the sup-norm is nonincreasing on Ioo 0 T.
    intro _p' _hχ _ha _hb
    exact {
      continuousOn := by rw [hsup_fun_eq]; exact continuousOn_const
      differentiableOn := by rw [hsup_fun_eq]; exact differentiableOn_const c
      deriv_nonpos := by
        intro t _ht
        rw [hsup_fun_eq]; simp [deriv_const]
    }

/-! ### The v-equation for the elliptic relation -/

/-- The v-equation is satisfied by v = (ν/μ)u^γ when both are spatially
constant, since the Laplacian vanishes and -μv + νu^γ = 0. -/
lemma ellipticV_pde (p : CM2Params) (c : ℝ) (_hc : 0 < c)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    (0 : ℝ) = intervalDomainLaplacian (fun _ : intervalDomainPoint => ellipticV p c) x
      - p.μ * ellipticV p c + p.ν * c ^ p.γ := by
  rw [intervalDomainLaplacian_const_zero (ellipticV p c) hx]
  unfold ellipticV
  field_simp [ne_of_gt p.hμ]
  ring

/-! ### Time derivative for constant-in-time solutions -/

/-- The time derivative of a constant-in-time function is zero. -/
lemma timeDeriv_const (c : ℝ) (t : ℝ) (_x : intervalDomainPoint) :
    deriv (fun _s : ℝ => c) t = (0 : ℝ) :=
  deriv_const t c

/-! ### The equilibrium existence theorem

When a > 0 and b > 0, the positive equilibrium c = (a/b)^{1/α} satisfies
c(a - bc^α) = 0 because c^α = a/b.

When a = 0 and b = 0, any positive c satisfies c(0 - 0·c^α) = 0. -/

/-- The equilibrium value (a/b)^{1/α} is positive when a > 0 and b > 0. -/
lemma equilibrium_pos (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    0 < (p.a / p.b) ^ (1 / p.α) := by
  exact Real.rpow_pos_of_pos (div_pos ha hb) _

/-- At equilibrium c = (a/b)^{1/α}, we have c^α = a/b. -/
lemma equilibrium_rpow (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    ((p.a / p.b) ^ (1 / p.α)) ^ p.α = p.a / p.b := by
  rw [← Real.rpow_mul (le_of_lt (div_pos ha hb))]
  rw [one_div, inv_mul_cancel₀ (ne_of_gt p.hα)]
  exact Real.rpow_one _

/-- At equilibrium, the reaction term a - b·c^α vanishes. -/
lemma equilibrium_reaction_zero (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    p.a - p.b * ((p.a / p.b) ^ (1 / p.α)) ^ p.α = 0 := by
  rw [equilibrium_rpow p ha hb, mul_div_cancel₀ _ (ne_of_gt hb), sub_self]

/-- Existence of a positive equilibrium classical solution on intervalDomain
when `0 < a` and `0 < b`.  The solution is u(t,x) = (a/b)^{1/α} and
v(t,x) = (ν/μ)·((a/b)^{1/α})^γ, constant in both time and space. -/
theorem equilibrium_isPaper2ClassicalSolution
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    ∀ T > 0, IsPaper2ClassicalSolution intervalDomain p T
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      (fun _ (_ : intervalDomainPoint) =>
        ellipticV p ((p.a / p.b) ^ (1 / p.α))) := by
  intro T hT
  set c := (p.a / p.b) ^ (1 / p.α) with hc_def
  have hc : 0 < c := equilibrium_pos p ha hb
  exact IsPaper2ClassicalSolution.of_components hT
    -- regularity
    (constantInTime_classicalRegularity hc hT p)
    -- positivity
    (fun _t _x _ht0 _htT _hx => hc)
    -- u-PDE: timeDeriv = laplacian - χ₀·chemtaxisDiv + u(a - bu^α)
    (fun t x ht0 htT hx => by
      -- timeDeriv u t x = deriv (fun s => c) t = 0
      change deriv (fun s : ℝ => c) t =
        intervalDomainLaplacian (fun _ => c) x
          - p.χ₀ * intervalDomainChemotaxisDiv p (fun _ => c)
              (fun _ => ellipticV p c) x
          + c * (p.a - p.b * c ^ p.α)
      rw [deriv_const, intervalDomainLaplacian_const_zero c hx,
        intervalDomainChemotaxisDiv_const_zero p c (ellipticV p c) hx,
        equilibrium_reaction_zero p ha hb]
      ring)
    -- v-PDE: 0 = laplacian v - μv + νu^γ
    (fun t x ht0 htT hx => by
      change (0 : ℝ) =
        intervalDomainLaplacian (fun _ => ellipticV p c) x
          - p.μ * ellipticV p c + p.ν * c ^ p.γ
      exact ellipticV_pde p c hc hx)
    -- Neumann BC
    (fun t x ht0 htT hx => by
      exact ⟨intervalDomainNormalDeriv_const_zero c hx,
             intervalDomainNormalDeriv_const_zero (ellipticV p c) hx⟩)

/-- Existence of a positive constant classical solution on intervalDomain
when `a = 0` and `b = 0`.  For any c > 0, u(t,x) = c and
v(t,x) = (ν/μ)c^γ solve the PDE because the reaction term
c(0 - 0·c^α) = 0 vanishes. -/
theorem zeroReaction_isPaper2ClassicalSolution
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    (c : ℝ) (hc : 0 < c) :
    ∀ T > 0, IsPaper2ClassicalSolution intervalDomain p T
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c) := by
  intro T hT
  exact IsPaper2ClassicalSolution.of_components hT
    (constantInTime_classicalRegularity hc hT p)
    (fun _t _x _ht0 _htT _hx => hc)
    -- u-PDE
    (fun t x ht0 htT hx => by
      change deriv (fun s : ℝ => c) t =
        intervalDomainLaplacian (fun _ => c) x
          - p.χ₀ * intervalDomainChemotaxisDiv p (fun _ => c)
              (fun _ => ellipticV p c) x
          + c * (p.a - p.b * c ^ p.α)
      rw [deriv_const, intervalDomainLaplacian_const_zero c hx,
        intervalDomainChemotaxisDiv_const_zero p c (ellipticV p c) hx,
        ha, hb]
      simp)
    -- v-PDE
    (fun t x ht0 htT hx => ellipticV_pde p c hc hx)
    -- Neumann BC
    (fun t x ht0 htT hx =>
      ⟨intervalDomainNormalDeriv_const_zero c hx,
       intervalDomainNormalDeriv_const_zero (ellipticV p c) hx⟩)

/-- Combined local existence theorem: for any CM2Params with either
(a > 0 ∧ b > 0) or (a = 0 ∧ b = 0), there exists a positive classical
solution on intervalDomain for all T > 0 (in fact, a global solution). -/
theorem constantSolution_globalExistence
    (p : CM2Params) (h : (0 < p.a ∧ 0 < p.b) ∨ (p.a = 0 ∧ p.b = 0)) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨_, _, equilibrium_isPaper2ClassicalSolution p ha hb⟩
  · exact ⟨_, _, zeroReaction_isPaper2ClassicalSolution p ha hb 1 one_pos⟩

/-- InitialTrace for the constant solution u(t,x) = c with u₀ = constOnInterval c.
Since u(t) - u₀ = 0, the sup norm is 0 < ε for any ε > 0. -/
theorem constantSolution_initialTrace (c : ℝ) :
    InitialTrace intervalDomain (constOnInterval c)
      (fun _ _ => c) := by
  intro ε hε
  refine ⟨1, one_pos, fun t _ht0 _htδ => ?_⟩
  change intervalDomainSupNorm (fun x => c - c) < ε
  have hzero : (fun _ : intervalDomainPoint => c - c) = fun _ => 0 := by
    ext; ring
  rw [hzero, intervalDomainSupNorm_const, abs_zero]
  exact hε

/-- Partial `IntervalDomainExistence` for constant initial data when
(a > 0, b > 0) or (a = 0, b = 0). Produces the equilibrium / constant
solution as a classical solution with InitialTrace. -/
theorem constantSolution_localExistence_with_trace
    (p : CM2Params)
    (h : (0 < p.a ∧ 0 < p.b) ∨ (p.a = 0 ∧ p.b = 0)) :
    ∃ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ ∧
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · set c := (p.a / p.b) ^ (1 / p.α)
    have hc : 0 < c := Real.rpow_pos_of_pos (div_pos ha hb) _
    refine ⟨constOnInterval c, constOnInterval_pos hc, 1, one_pos,
      fun _ _ => c, fun _ _ => ellipticV p c, ?_, ?_⟩
    · exact (equilibrium_isPaper2ClassicalSolution p ha hb) 1 one_pos
    · exact constantSolution_initialTrace c
  · refine ⟨constOnInterval 1, constOnInterval_pos one_pos, 1, one_pos,
      fun _ _ => 1, fun _ _ => ellipticV p 1, ?_, ?_⟩
    · exact (zeroReaction_isPaper2ClassicalSolution p ha hb 1 one_pos) 1 one_pos
    · exact constantSolution_initialTrace 1

end ShenWork.IntervalDomainExistence

end
