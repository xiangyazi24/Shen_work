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

/-! ### Mild solution operator on intervalDomain

The Duhamel integral formulation for u on [0,1]:
  u(t,x) = (e^{tΔ_N} u₀)(x) + ∫₀ᵗ (e^{(t-s)Δ_N} F(u(s)))(x) ds

where e^{tΔ_N} is the Neumann heat semigroup (intervalSemigroupOperator)
and F(u)(x) = u(x)(a - b·u(x)^α) is the logistic source.

For the local existence to work on intervalDomain, we need:
1. Semigroup L^∞ contractivity: ‖e^{tΔ} f‖_∞ ≤ ‖f‖_∞ (DONE)
2. Lipschitz bound on F (DONE in MildSolution.lean for the whole line)
3. Contraction of the Duhamel map for small T
4. Fixed point → mild solution
5. Regularity bootstrap: mild → classical (OPEN — genuine PDE content)

Current status: steps 1-2 are done, step 3 is provable from existing tools,
step 5 is the honest analytical frontier. -/

/-- The logistic reaction source F(u)(x) = u(x)(a - b·u(x)^α) on
intervalDomainPoint. -/
def intervalLogisticSource (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (x : intervalDomainPoint) : ℝ :=
  u x * (p.a - p.b * (u x) ^ p.α)

/-- The Duhamel mild solution operator on intervalDomain:
Φ(u)(t)(x) = (e^{tΔ_N} u₀)(x) + ∫₀ᵗ (e^{(t-s)Δ_N} F(u(s)))(x) ds

This defines a map from trajectories u : ℝ → (intervalDomainPoint → ℝ)
to trajectories, whose fixed point is a mild solution. -/
def intervalDuhamelOperator (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1 +
    ∫ s in Set.Icc 0 t,
      intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalLogisticSource p (u s))) x.1

/-- The logistic source F(u) = u(a - bu^α) is Lipschitz on bounded sets.
For |u₁|, |u₂| ≤ M: |F(u₁) - F(u₂)| ≤ L · |u₁ - u₂| where
L depends on a, b, α, M. -/
theorem intervalLogisticSource_lipschitz (p : CM2Params) {M : ℝ} (hM : 0 < M) :
    ∃ L > 0, ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
    |u₁ * (p.a - p.b * u₁ ^ p.α) - u₂ * (p.a - p.b * u₂ ^ p.α)| ≤
      L * |u₁ - u₂| := by
  -- F(u) = a·u - b·u^{α+1}, F'(u) = a - b(α+1)u^α
  -- |F'(u)| ≤ a + b(α+1)M^α + 1 =: L on [-M, M]
  have hα_pos : 0 < p.α := p.hα
  have hα0 : 0 ≤ p.α := hα_pos.le
  have hα1 : 1 ≤ p.α + 1 := by linarith
  have hM0 : 0 ≤ M := le_of_lt hM
  have hMpow_pos : 0 < M ^ p.α := Real.rpow_pos_of_pos hM p.α
  set C := p.a + p.b * (p.α + 1) * M ^ p.α + 1 with hC_def
  have hC_pos : 0 < C := by
    have : 0 ≤ p.b * (p.α + 1) * M ^ p.α :=
      mul_nonneg (mul_nonneg p.hb (by linarith : 0 ≤ p.α + 1)) hMpow_pos.le
    linarith [p.ha]
  refine ⟨C, hC_pos, ?_⟩
  intro u₁ u₂ hu₁ hu₂
  -- Define f and its pointwise derivative
  let f : ℝ → ℝ := fun x => p.a * x - p.b * x ^ (p.α + 1)
  let fp : ℝ → ℝ := fun x => p.a - p.b * ((p.α + 1) * x ^ p.α)
  have hu₁s : u₁ ∈ Set.Icc (-M) M := abs_le.mp hu₁
  have hu₂s : u₂ ∈ Set.Icc (-M) M := abs_le.mp hu₂
  -- f agrees with u * (a - b * u^α) for all u
  have hf_eq : ∀ u : ℝ, f u = u * (p.a - p.b * u ^ p.α) := by
    intro u
    simp only [f]
    by_cases hu : u = 0
    · subst hu; simp [Real.zero_rpow (ne_of_gt (by linarith : (0 : ℝ) < p.α + 1))]
    · have : u ^ (p.α + 1) = u * u ^ p.α := by
        rw [Real.rpow_add_one hu]; ring
      rw [this]; ring
  -- HasDerivWithinAt for f
  have hder : ∀ x ∈ Set.Icc (-M) M,
      HasDerivWithinAt f (fp x) (Set.Icc (-M) M) x := by
    intro x _hx
    have hp : HasDerivAt (fun y : ℝ => y ^ (p.α + 1)) ((p.α + 1) * x ^ p.α) x := by
      have h := Real.hasDerivAt_rpow_const (x := x) (p := p.α + 1) (Or.inr hα1)
      simp only [show p.α + 1 - 1 = p.α from by ring] at h
      exact h
    have hF : HasDerivAt f (fp x) x := by
      have h1 := hasDerivAt_id x |>.const_mul p.a
      have h2 := hp.const_mul p.b
      have := h1.sub h2
      convert this using 1; simp [fp]
    exact hF.hasDerivWithinAt
  -- Bound |fp(x)| ≤ C on [-M, M]
  have hbound : ∀ x ∈ Set.Icc (-M) M, ‖fp x‖ ≤ C := by
    intro x hx
    have hxabs : |x| ≤ M := abs_le.mpr hx
    have hxpow : |x ^ p.α| ≤ M ^ p.α := by
      calc |x ^ p.α| ≤ |x| ^ p.α := Real.abs_rpow_le_abs_rpow x p.α
        _ ≤ M ^ p.α := Real.rpow_le_rpow (abs_nonneg x) hxabs hα0
    have hcoeff_nn : 0 ≤ p.b * ((p.α + 1) * |x ^ p.α|) :=
      mul_nonneg p.hb (mul_nonneg (by linarith : 0 ≤ p.α + 1) (abs_nonneg _))
    simp only [fp, C, Real.norm_eq_abs]
    calc |p.a - p.b * ((p.α + 1) * x ^ p.α)|
        ≤ |p.a| + |p.b * ((p.α + 1) * x ^ p.α)| := by
          calc |p.a - p.b * ((p.α + 1) * x ^ p.α)|
              = |p.a + (-(p.b * ((p.α + 1) * x ^ p.α)))| := by ring_nf
            _ ≤ |p.a| + |-(p.b * ((p.α + 1) * x ^ p.α))| := abs_add_le _ _
            _ = |p.a| + |p.b * ((p.α + 1) * x ^ p.α)| := by rw [abs_neg]
      _ = p.a + p.b * ((p.α + 1) * |x ^ p.α|) := by
          rw [abs_of_nonneg p.ha, abs_mul, abs_mul,
              abs_of_nonneg p.hb, abs_of_nonneg (by linarith : 0 ≤ p.α + 1)]
      _ ≤ p.a + p.b * ((p.α + 1) * M ^ p.α) := by
          have : p.b * ((p.α + 1) * |x ^ p.α|) ≤ p.b * ((p.α + 1) * M ^ p.α) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hxpow (by linarith : 0 ≤ p.α + 1)) p.hb
          linarith
      _ ≤ C := by simp [hC_def]; ring_nf; linarith
  -- Apply mean value theorem
  have hmv : ‖f u₁ - f u₂‖ ≤ C * ‖u₁ - u₂‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hbound (convex_Icc (-M) M) hu₂s hu₁s
  rw [hf_eq u₁, hf_eq u₂] at hmv
  simpa [Real.norm_eq_abs] using hmv

/-! ### Mild solution data and conditional local existence

The full local existence theorem for arbitrary positive initial data
requires constructing a mild solution (Duhamel fixed point) and then
bootstrapping its regularity to a classical solution.  We factor this
into a **conditional** result:

1. `IsMildSolutionData` is a Prop-valued predicate bundling the genuine
   PDE hypotheses on `(u, v)`: Duhamel fixed point, pointwise PDE,
   positivity, Neumann BC, classical regularity, initial trace.

2. `localExistence_of_isMildSolutionData` assembles these into
   `IsPaper2ClassicalSolution ∧ InitialTrace`.

3. `localExistence_conditional` states:
   if one can always produce `IsMildSolutionData` from positive initial
   data, then the full local existence holds.

The honest gap is the hypothesis `hmild`: constructing `(u, v)` satisfying
`IsMildSolutionData` requires Banach contraction (fixed point), regularity
bootstrap (mild to classical), maximum principle (sup-norm decay), and
positivity (comparison/strong maximum principle).  Each of these is real
PDE analysis. -/

/-- Predicate asserting that `(u, v)` form a mild solution on `[0, T]`
with initial datum `u₀`.  Each conjunct is a genuine PDE result:
- `duhamel_fixed`: `u` is a fixed point of the Duhamel operator
- `pde_u`, `pde_v`: the PDE holds pointwise (regularity bootstrap)
- `pos`: solution is strictly positive in the interior (maximum principle)
- `neumann`: Neumann boundary conditions
- `regularity`: sup-norm derivative condition for the max principle chain
- `trace`: initial data is attained continuously in sup-norm -/
def IsMildSolutionData (p : CM2Params) (T : ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) : Prop :=
  -- u is a fixed point of the Duhamel operator
  (∀ t x, 0 ≤ t → t ≤ T →
    u t x = intervalDuhamelOperator p u₀ u t x) ∧
  -- Positivity of u in the interior
  (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside → 0 < u t x) ∧
  -- The u-equation holds pointwise (regularity bootstrap)
  (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    intervalDomain.timeDeriv u t x =
      intervalDomain.laplacian (u t) x
        - p.χ₀ * intervalDomain.chemotaxisDiv p (u t) (v t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α)) ∧
  -- The v-equation holds pointwise
  (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    0 = intervalDomain.laplacian (v t) x
      - p.μ * v t x + p.ν * (u t x) ^ p.γ) ∧
  -- Neumann boundary conditions
  (∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
    intervalDomain.normalDeriv (u t) x = 0 ∧
    intervalDomain.normalDeriv (v t) x = 0) ∧
  -- Classical regularity (sup-norm derivative condition)
  intervalDomainClassicalRegularity T u v ∧
  -- Initial trace: u(t) → u₀ as t → 0⁺ in sup-norm
  InitialTrace intervalDomain u₀ u

/-- Assembly: `IsMildSolutionData` directly yields
`IsPaper2ClassicalSolution ∧ InitialTrace`.

The conjuncts of `IsMildSolutionData` are exactly what is needed for
`IsPaper2ClassicalSolution.of_components` plus `InitialTrace`. -/
theorem localExistence_of_isMildSolutionData
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (_hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hdata : IsMildSolutionData p T u₀ u v) :
    ∃ Tmax > 0, ∃ u' v' : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u' v' ∧
      InitialTrace intervalDomain u₀ u' :=
  ⟨T, hT, u, v,
    IsPaper2ClassicalSolution.of_components hT
      hdata.2.2.2.2.2.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1,
    hdata.2.2.2.2.2.2⟩

/-- Conditional local existence for intervalDomain.

If for every positive initial datum one can construct a mild solution
(i.e., produce a Duhamel fixed point with the required regularity,
positivity, PDE, boundary conditions, and initial trace), then the full
local existence theorem holds.

The honest gap is the hypothesis `hmild`: constructing a mild solution
from the Duhamel fixed point requires:
  (1) Banach contraction on a complete metric space of trajectories
  (2) Regularity bootstrap: mild solution satisfies the PDE pointwise
  (3) Maximum principle: sup-norm derivative control
  (4) Comparison / strong maximum principle: strict positivity
Each of these is a genuine PDE result. -/
theorem localExistence_conditional
    (p : CM2Params)
    (hmild : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsMildSolutionData p T u₀ u v) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨T, hT, u, v, hdata⟩ := hmild u₀ hu₀
  exact localExistence_of_isMildSolutionData p u₀ hu₀ hT hdata

/-! ### Duhamel contraction: abstract integral bound

The key estimate for Banach contraction: if the source difference
is pointwise bounded by C, then the Duhamel integral difference is
bounded by C · T (via the sub-Markov property of the heat semigroup
and the integral mean value bound).

This is stated abstractly, without reference to the specific semigroup,
as a bound on integrals of bounded functions. -/

/-- If a real-valued function is bounded by C on [0,t], its integral
is bounded by C·t. This is the elementary version of the Duhamel
contraction estimate. -/
theorem integral_Icc_bound_of_pointwise_bound
    {h : ℝ → ℝ} {C t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ s, s ∈ Set.Icc 0 t → |h s| ≤ C) :
    |∫ s in Set.Icc 0 t, h s| ≤ C * t := by
  have hvol : MeasureTheory.volume (Set.Icc (0 : ℝ) t) < ⊤ := by
    simp [Real.volume_Icc]
  have hnorm_bound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖h s‖ ≤ C :=
    fun s hs => by rw [Real.norm_eq_abs]; exact hbound s hs
  calc |∫ s in Set.Icc 0 t, h s|
      = ‖∫ s in Set.Icc 0 t, h s‖ := (Real.norm_eq_abs _).symm
    _ ≤ C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hvol hnorm_bound
    _ = C * t := by
        congr 1
        simp [MeasureTheory.Measure.real, Real.volume_Icc, ht]

/-! ### Duhamel contraction estimate with semigroup L∞ bound

The key contraction estimate for the Banach fixed-point argument:
if the source differences `G(s,y)` are uniformly bounded by `C` and
the Neumann heat semigroup is L∞-contractive (which it is, via the
sub-Markov property), then the Duhamel integral

  ∫₀ᵗ e^{(t-s)Δ_N} G(s) ds

is bounded pointwise by `C·T` for `t ∈ [0,T]`.

Combined with the Lipschitz bound on the logistic source
(`intervalLogisticSource_lipschitz`), this gives:
if `|u₁(s,y) - u₂(s,y)| ≤ D` for all `(s,y)`,
then `|Φ(u₁)(t,x) - Φ(u₂)(t,x)| ≤ Lip·D·T`.
For `T < 1/Lip`, this makes Φ a contraction. -/

/-- The Neumann heat semigroup on `[0,L]` is L∞-contractive:
if `|f(y)| ≤ M` for all `y`, then `|e^{tΔ_N} f(x)| ≤ M`
for all `x` and `t > 0`.  This is a direct consequence of the
sub-Markov property (kernel mass ≤ 1).

This is a repackaging of `intervalSemigroupOperator_Linfty_bound`
in a form convenient for the Duhamel contraction. -/
theorem semigroup_Linfty_contraction
    {L τ : ℝ} (hτ : 0 < τ)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M)
    (x : ℝ) :
    |intervalSemigroupOperator L τ f x| ≤ M :=
  intervalSemigroupOperator_Linfty_bound hτ hM hf x

/-- **Duhamel contraction estimate (pointwise form).**

If the source difference `G(s,·)` is uniformly bounded by `C` for
all `s ∈ [0,T]`, then the Duhamel integral

  `∫ s in [0,t], e^{(t-s)Δ_N} G(s)(x) ds`

is bounded in absolute value by `C · T` for any `t ∈ [0,T]` and
any spatial point `x`.

**Proof sketch:**
- For a.e. `s ∈ [0,t]` (all except `s = t`, which is a null set),
  we have `t - s > 0`, so the L∞ bound applies:
  `|e^{(t-s)Δ} G(s)(x)| ≤ C`.
- By `norm_setIntegral_le_of_norm_le_const_ae`, the integral norm
  is `≤ C · vol([0,t]) = C · t ≤ C · T`. -/
theorem duhamel_contraction_pointwise
    {G : ℝ → ℝ → ℝ} {C T : ℝ} (_hT : 0 < T) (hC : 0 ≤ C)
    (hG_bound : ∀ s, 0 ≤ s → s ≤ T → ∀ y, |G s y| ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (x : ℝ) :
    |∫ s in Set.Icc 0 t,
      intervalSemigroupOperator 1 (t - s) (G s) x| ≤ C * T := by
  -- The integrand is bounded by C a.e. on [0,t]:
  -- for s < t, the semigroup L∞ bound applies; s = t is null.
  have hae_bound : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.Icc (0 : ℝ) t →
        ‖intervalSemigroupOperator 1 (t - s) (G s) x‖ ≤ C := by
    have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        s ≠ t := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Real.norm_eq_abs]
    have hs0 : 0 ≤ s := hs_mem.1
    have hst : s ≤ t := hs_mem.2
    have hsT : s ≤ T := le_trans hst htT
    have hts_pos : 0 < t - s := by
      exact sub_pos.mpr (lt_of_le_of_ne hst hs_ne)
    exact intervalSemigroupOperator_Linfty_bound hts_pos hC (hG_bound s hs0 hsT) x
  -- The set [0,t] has finite measure
  have hvol_fin : MeasureTheory.volume (Set.Icc (0 : ℝ) t) < ⊤ :=
    measure_Icc_lt_top
  -- Apply the norm bound for set integrals
  have hstep1 : ‖∫ s in Set.Icc (0 : ℝ) t,
      intervalSemigroupOperator 1 (t - s) (G s) x‖ ≤
        C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' hvol_fin hae_bound
  -- Compute volume.real [0,t] = t
  have hvol_eq : MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) = t := by
    simp [MeasureTheory.Measure.real, Real.volume_Icc, ht0]
  -- Chain: |integral| = ‖integral‖ ≤ C·t ≤ C·T
  calc |∫ s in Set.Icc (0 : ℝ) t,
        intervalSemigroupOperator 1 (t - s) (G s) x|
      = ‖∫ s in Set.Icc (0 : ℝ) t,
          intervalSemigroupOperator 1 (t - s) (G s) x‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) := hstep1
    _ = C * t := by rw [hvol_eq]
    _ ≤ C * T := by exact mul_le_mul_of_nonneg_left htT hC

/-- **Duhamel operator difference bound.**

For two trajectories `u₁`, `u₂`, if the semigroup-propagated source
differences are pointwise bounded by `C` a.e. on `[0,t]`, and the
time integrands are integrable, then:

  `|Φ(u₁)(t,x) - Φ(u₂)(t,x)| ≤ C · T`

In practice, the pointwise bound `hpointwise` is obtained by combining:
- The source Lipschitz bound `|F(u₁) - F(u₂)| ≤ Lip · |u₁ - u₂|`
- The semigroup linearity `S(τ)(f₁ - f₂) = S(τ)f₁ - S(τ)f₂`
- The semigroup L∞ bound `|S(τ)g(x)| ≤ sup|g|`

For `C = Lip · D` (where `D = sup|u₁ - u₂|`), the bound becomes
`Lip · D · T`, and for `T < 1/Lip` this makes `Φ` a strict contraction
with constant `Lip · T < 1`. -/
theorem duhamelOperator_diff_bound
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u₁ u₂ : ℝ → intervalDomainPoint → ℝ)
    {C T : ℝ} (_hT : 0 < T) (hC : 0 ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    -- Integrability of both time integrands
    (hint₁ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hint₂ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    -- Pointwise bound on the difference of semigroup-propagated sources
    (hpointwise : ∀ s, s ∈ Set.Icc 0 t → s ≠ t →
      |intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1 -
       intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1| ≤ C) :
    |intervalDuhamelOperator p u₀ u₁ t x -
     intervalDuhamelOperator p u₀ u₂ t x| ≤ C * T := by
  -- Unfold and cancel the initial data term
  simp only [intervalDuhamelOperator, add_sub_add_left_eq_sub]
  -- Use ∫f₁ - ∫f₂ = ∫(f₁ - f₂)
  rw [← MeasureTheory.integral_sub hint₁ hint₂]
  -- The integrand is bounded by C a.e. on [0,t]
  have hae_bound : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.Icc (0 : ℝ) t →
        ‖(intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1 -
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1)‖ ≤ C := by
    have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        s ≠ t := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Real.norm_eq_abs]
    exact hpointwise s hs_mem hs_ne
  -- Bound the integral
  have hvol_fin : MeasureTheory.volume (Set.Icc (0 : ℝ) t) < ⊤ :=
    measure_Icc_lt_top
  have hstep : ‖∫ s in Set.Icc (0 : ℝ) t,
      (intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1 -
       intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1)‖ ≤
        C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' hvol_fin hae_bound
  have hvol_eq : MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) = t := by
    simp [MeasureTheory.Measure.real, Real.volume_Icc, ht0]
  calc |∫ s in Set.Icc (0 : ℝ) t,
        (intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1 -
         intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1)|
      = ‖∫ s in Set.Icc (0 : ℝ) t,
          (intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1 -
           intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) := hstep
    _ = C * t := by rw [hvol_eq]
    _ ≤ C * T := mul_le_mul_of_nonneg_left htT hC

/-! ### Lifted source bounds for the Duhamel contraction

The contraction argument needs to bound the lifted source difference
`|intervalDomainLift (F(u₁(s))) y - intervalDomainLift (F(u₂(s))) y|`
in terms of `sup|u₁(s) - u₂(s)|`.  We factor this into:

1. `intervalDomainLift_abs_le`: the lift preserves pointwise absolute bounds.
2. `intervalDomainLift_diff_abs_le`: the lift of a difference is bounded by
   the pointwise difference bound.
3. `intervalLogisticSource_lift_diff_bound`: the lifted source difference is
   bounded by `Lip · D` where Lip is the source Lipschitz constant and
   D = sup|u₁ - u₂|.
4. `duhamel_contraction_full`: the complete contraction estimate
   |Φ(u₁)(t,x) - Φ(u₂)(t,x)| ≤ Lip · T · D.
5. `contraction_factor_lt_one`: the strict contraction property for small T. -/

/-- The lift of a function on intervalDomainPoint preserves absolute
value bounds: if `|f(y)| ≤ C` for all `y : intervalDomainPoint`, then
`|intervalDomainLift f x| ≤ C` for all `x : ℝ`. -/
theorem intervalDomainLift_abs_le
    {f : intervalDomainPoint → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y : intervalDomainPoint, |f y| ≤ C) :
    ∀ x : ℝ, |intervalDomainLift f x| ≤ C := by
  intro x
  unfold intervalDomainLift
  split_ifs with hx
  · exact hf ⟨x, hx⟩
  · simp only [abs_zero]; exact hC

/-- The lift preserves pointwise difference bounds: if
`|f(y) - g(y)| ≤ D` for all `y : intervalDomainPoint`, then
`|intervalDomainLift f x - intervalDomainLift g x| ≤ D` for all `x : ℝ`. -/
theorem intervalDomainLift_diff_abs_le
    {f g : intervalDomainPoint → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hfg : ∀ y : intervalDomainPoint, |f y - g y| ≤ D) :
    ∀ x : ℝ, |intervalDomainLift f x - intervalDomainLift g x| ≤ D := by
  intro x
  unfold intervalDomainLift
  split_ifs with hx
  · exact hfg ⟨x, hx⟩
  · simp only [sub_self, abs_zero]; exact hD

/-- The logistic source is pointwise Lipschitz: given the Lipschitz constant
from `intervalLogisticSource_lipschitz`, the source difference at each
spatial point is bounded by `L · |u₁(y) - u₂(y)|`. -/
theorem intervalLogisticSource_pointwise_lipschitz
    (p : CM2Params) {M L : ℝ}
    (hL_lip : ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
      |u₁ * (p.a - p.b * u₁ ^ p.α) - u₂ * (p.a - p.b * u₂ ^ p.α)| ≤
        L * |u₁ - u₂|)
    {u₁ u₂ : intervalDomainPoint → ℝ}
    (hu₁ : ∀ y, |u₁ y| ≤ M) (hu₂ : ∀ y, |u₂ y| ≤ M)
    (y : intervalDomainPoint) :
    |intervalLogisticSource p u₁ y - intervalLogisticSource p u₂ y| ≤
      L * |u₁ y - u₂ y| := by
  unfold intervalLogisticSource
  exact hL_lip (u₁ y) (u₂ y) (hu₁ y) (hu₂ y)

/-- The lifted source difference is bounded by `Lip · D` where
`D` is the uniform trajectory difference and `Lip` is the Lipschitz
constant of the logistic source on the ball of radius M.

This combines:
- The pointwise Lipschitz bound on `intervalLogisticSource`
- The lift bound `intervalDomainLift_diff_abs_le`
- The uniform trajectory difference `|u₁(s,y) - u₂(s,y)| ≤ D` -/
theorem intervalLogisticSource_lift_diff_bound
    (p : CM2Params) {M L : ℝ} (hL : 0 ≤ L)
    (hL_lip : ∀ u₁ u₂ : ℝ, |u₁| ≤ M → |u₂| ≤ M →
      |u₁ * (p.a - p.b * u₁ ^ p.α) - u₂ * (p.a - p.b * u₂ ^ p.α)| ≤
        L * |u₁ - u₂|)
    {u₁ u₂ : intervalDomainPoint → ℝ}
    (hu₁ : ∀ y, |u₁ y| ≤ M) (hu₂ : ∀ y, |u₂ y| ≤ M)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiff : ∀ y, |u₁ y - u₂ y| ≤ D) :
    ∀ x : ℝ,
      |intervalDomainLift (intervalLogisticSource p u₁) x -
       intervalDomainLift (intervalLogisticSource p u₂) x| ≤ L * D := by
  have hLD : 0 ≤ L * D := mul_nonneg hL hD
  apply intervalDomainLift_diff_abs_le hLD
  intro y
  calc |intervalLogisticSource p u₁ y - intervalLogisticSource p u₂ y|
      ≤ L * |u₁ y - u₂ y| :=
        intervalLogisticSource_pointwise_lipschitz p hL_lip hu₁ hu₂ y
    _ ≤ L * D := mul_le_mul_of_nonneg_left (hdiff y) hL

/-- **Full Duhamel contraction estimate.**

If `|u₁(s,y) - u₂(s,y)| ≤ D` for all `(s,y)` with `s ∈ [0,T]`,
and the logistic source has Lipschitz constant `L` on the ball of
radius `M`, then

  `|Φ(u₁)(t,x) - Φ(u₂)(t,x)| ≤ L · T · D`

for all `t ∈ [0,T]` and `x`.

This is the key step for Banach fixed point: choosing `T < 1/L`
makes Φ a strict contraction with factor `L·T < 1`.

The hypotheses `hint₁`, `hint₂` require integrability of the Duhamel
integrands; this is a measurability condition that follows from
regularity of the trajectories. -/
theorem duhamel_contraction_full
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u₁ u₂ : ℝ → intervalDomainPoint → ℝ)
    {M L D T : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    (hu₁ : ∀ s y, |u₁ s y| ≤ M)
    (hu₂ : ∀ s y, |u₂ s y| ≤ M)
    (hdiff : ∀ s y, |u₁ s y - u₂ s y| ≤ D)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (hint₁ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hint₂ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    -- Integrability of the lifted sources against the interval measure,
    -- needed for the semigroup linearity S(τ)(f₁-f₂) = S(τ)f₁ - S(τ)f₂
    (hlift_int₁ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable (intervalDomainLift (intervalLogisticSource p (u₁ s)))
        (intervalMeasure 1))
    (hlift_int₂ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable (intervalDomainLift (intervalLogisticSource p (u₂ s)))
        (intervalMeasure 1)) :
    |intervalDuhamelOperator p u₀ u₁ t x -
     intervalDuhamelOperator p u₀ u₂ t x| ≤ L * D * T := by
  have hLD : 0 ≤ L * D := mul_nonneg hL hD
  -- The lifted source difference is bounded by L·D at each spatial point
  have hG_bound : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalLogisticSource p (u₁ s)) y -
       intervalDomainLift (intervalLogisticSource p (u₂ s)) y| ≤ L * D :=
    fun s _hs0 _hsT =>
      intervalLogisticSource_lift_diff_bound p hL hL_lip
        (hu₁ s) (hu₂ s) hD (hdiff s)
  -- The semigroup-propagated source differences are bounded by L·D
  -- (via L∞ contraction of the semigroup)
  have hpointwise : ∀ s, s ∈ Set.Icc 0 t → s ≠ t →
      |intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1 -
       intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1| ≤
        L * D := by
    intro s hs hst
    have hs0 : 0 ≤ s := hs.1
    have hsT : s ≤ T := le_trans hs.2 htT
    have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    exact intervalSemigroupOperator_contraction hts_pos hLD
      (hlift_int₁ s hs0 hsT) (hlift_int₂ s hs0 hsT)
      (hG_bound s hs0 hsT) x.1
  -- Apply the Duhamel operator difference bound with C = L·D
  exact duhamelOperator_diff_bound p u₀ u₁ u₂ hT hLD
    ht0 htT x hint₁ hint₂ hpointwise

/-- **Strict contraction factor.**

If `L · T < 1` and `D > 0`, then `L · T · D < D`.
This is the "gap" that makes the Duhamel map a strict contraction
in the Banach fixed point theorem. -/
theorem contraction_factor_strict
    {L T D : ℝ} (hD : 0 < D) (hLT : L * T < 1) :
    L * T * D < D := by
  calc L * T * D < 1 * D :=
        mul_lt_mul_of_pos_right hLT hD
    _ = D := one_mul D

/-- **Duhamel contraction: strict bound when `Lip · T < 1`.**

Combining the contraction estimate with the contraction factor:
the Duhamel difference is strictly less than the trajectory difference
whenever D > 0 and L·T < 1.  When D = 0, the estimate gives 0 ≤ 0
(the trajectories are equal, so no contraction is needed). -/
theorem duhamel_strict_contraction
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u₁ u₂ : ℝ → intervalDomainPoint → ℝ)
    {M L D T : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hD : 0 < D)
    (hLT : L * T < 1)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    (hu₁ : ∀ s y, |u₁ s y| ≤ M)
    (hu₂ : ∀ s y, |u₂ s y| ≤ M)
    (hdiff : ∀ s y, |u₁ s y - u₂ s y| ≤ D)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (hint₁ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalLogisticSource p (u₁ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hint₂ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalLogisticSource p (u₂ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int₁ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable (intervalDomainLift (intervalLogisticSource p (u₁ s)))
        (intervalMeasure 1))
    (hlift_int₂ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable (intervalDomainLift (intervalLogisticSource p (u₂ s)))
        (intervalMeasure 1)) :
    |intervalDuhamelOperator p u₀ u₁ t x -
     intervalDuhamelOperator p u₀ u₂ t x| < D := by
  calc |intervalDuhamelOperator p u₀ u₁ t x -
        intervalDuhamelOperator p u₀ u₂ t x|
      ≤ L * D * T :=
        duhamel_contraction_full p u₀ u₁ u₂ hT hL hD.le hL_lip
          hu₁ hu₂ hdiff ht0 htT x hint₁ hint₂ hlift_int₁ hlift_int₂
    _ = L * T * D := by ring
    _ < D := contraction_factor_strict hD hLT

/-- **Existence of contraction time.**

For any positive Lipschitz constant `L`, there exists a time `T > 0`
such that `L · T < 1`, making the Duhamel operator a strict contraction.
This is the starting point for the Banach fixed-point argument. -/
theorem exists_contraction_time {L : ℝ} (hL : 0 < L) :
    ∃ T > 0, L * T < 1 := by
  refine ⟨1 / (2 * L), by positivity, ?_⟩
  have hL_ne : L ≠ 0 := ne_of_gt hL
  field_simp
  linarith

/-- **Contraction implies uniqueness of the Duhamel fixed point
on [0,T].**

If the Duhamel contraction estimate holds with `Lip · T < 1` and two
trajectories `u₁`, `u₂` are both fixed points of `Φ` (meaning
`u_i(t,x) = Φ(u_i)(t,x)` for all `(t,x)` in `[0,T]`), then they
are equal pointwise on `[0,T]`.

This is a consequence of the contraction: if D = sup|u₁ - u₂| > 0,
then D ≤ Lip·T·D < D, a contradiction. -/
theorem duhamel_fixed_point_unique
    {L T D : ℝ} (_hL : 0 ≤ L) (_hT : 0 < T) (hD : 0 ≤ D)
    (hLT : L * T < 1)
    (hcontraction : D ≤ L * T * D) :
    D = 0 := by
  by_contra hne
  have hD_pos : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
  have : L * T * D < D := contraction_factor_strict hD_pos hLT
  linarith

/-! ### Source absolute value bound on bounded sets

The logistic source `F(u) = u(a - bu^α)` is bounded in absolute value
on bounded sets: if `|u| ≤ M`, then `|F(u)| ≤ M · (a + b · M^α)`.
This is the bound needed for the ball invariance of the Duhamel operator. -/

/-- Pointwise bound on the logistic source: if `|u(y)| ≤ M`, then
`|F(u)(y)| ≤ M · (a + b · M^α)`.  Uses the triangle inequality
and monotonicity of `rpow`. -/
theorem intervalLogisticSource_abs_bound
    (p : CM2Params) {M : ℝ} (hM : 0 < M)
    {u : intervalDomainPoint → ℝ}
    (hu : ∀ y, |u y| ≤ M) (y : intervalDomainPoint) :
    |intervalLogisticSource p u y| ≤ M * (p.a + p.b * M ^ p.α) := by
  unfold intervalLogisticSource
  have hMnn : 0 ≤ M := le_of_lt hM
  rw [abs_mul]
  have hpow_bound : |u y ^ p.α| ≤ M ^ p.α := by
    calc |u y ^ p.α| ≤ |u y| ^ p.α := Real.abs_rpow_le_abs_rpow _ _
      _ ≤ M ^ p.α := Real.rpow_le_rpow (abs_nonneg _) (hu y) p.hα.le
  have hterm : |p.a - p.b * u y ^ p.α| ≤ p.a + p.b * M ^ p.α := by
    calc |p.a - p.b * u y ^ p.α|
        ≤ |p.a| + |p.b * u y ^ p.α| := abs_sub _ _
      _ = p.a + p.b * |u y ^ p.α| := by
          rw [abs_of_nonneg p.ha, abs_mul, abs_of_nonneg p.hb]
      _ ≤ p.a + p.b * M ^ p.α := by
          linarith [mul_le_mul_of_nonneg_left hpow_bound p.hb]
  calc |u y| * |p.a - p.b * u y ^ p.α|
      ≤ M * (p.a + p.b * M ^ p.α) :=
        mul_le_mul (hu y) hterm (abs_nonneg _) hMnn

/-- Lifted source bound: if `|u(y)| ≤ M` for all `y`, then the lift
of the source is also bounded by `M · (a + b · M^α)`. -/
theorem intervalLogisticSource_lift_abs_bound
    (p : CM2Params) {M : ℝ} (hM : 0 < M)
    {u : intervalDomainPoint → ℝ}
    (hu : ∀ y, |u y| ≤ M) :
    ∀ x : ℝ, |intervalDomainLift (intervalLogisticSource p u) x| ≤
      M * (p.a + p.b * M ^ p.α) := by
  have hS : 0 ≤ M * (p.a + p.b * M ^ p.α) := by
    apply mul_nonneg hM.le
    have : 0 ≤ p.b * M ^ p.α :=
      mul_nonneg p.hb (Real.rpow_nonneg hM.le _)
    linarith [p.ha]
  exact intervalDomainLift_abs_le hS
    (fun y => intervalLogisticSource_abs_bound p hM hu y)

/-! ### Duhamel ball invariance

The Duhamel operator maps the ball `{‖u‖ ≤ M}` to itself when:
- The initial data satisfies `|u₀(y)| ≤ H`
- The source is bounded by `S` on the ball
- `H + S · T ≤ M`

Combined with the semigroup L∞ contraction `|S(t)u₀(x)| ≤ H`,
the triangle inequality gives `|Φ(u)(t,x)| ≤ H + S·T ≤ M`. -/

/-- **Ball invariance for the Duhamel operator.**

For `0 < t ≤ T`, if:
1. `|u₀(y)| ≤ H` for all `y` (initial data bound via lift)
2. The source `|F(u(s))(y)| ≤ S` for all `s ∈ [0,T]`, `y` (via lift)
3. `H + S · T ≤ M`

Then `|Φ(u)(t,x)| ≤ M`. -/
theorem duhamel_ball_invariance
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {u : ℝ → intervalDomainPoint → ℝ}
    {M H S T : ℝ} (hT : 0 < T) (_hM : 0 ≤ M)
    (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ H)
    (hSource : ∀ s, 0 ≤ s → s ≤ T →
      ∀ y, |intervalDomainLift (intervalLogisticSource p (u s)) y| ≤ S)
    (hsum : H + S * T ≤ M)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint) :
    |intervalDuhamelOperator p u₀ u t x| ≤ M := by
  unfold intervalDuhamelOperator
  calc |intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1 +
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalLogisticSource p (u s))) x.1|
      ≤ |intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1| +
        |∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalLogisticSource p (u s))) x.1| :=
        abs_add_le _ _
    _ ≤ H + S * T := by
        have hterm1 : |intervalSemigroupOperator 1 t
            (intervalDomainLift u₀) x.1| ≤ H :=
          intervalSemigroupOperator_Linfty_bound ht0 hH hu₀ x.1
        have hterm2 : |∫ s in Set.Icc 0 t,
            intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalLogisticSource p (u s))) x.1|
            ≤ S * T :=
          duhamel_contraction_pointwise hT hS hSource ht0.le htT x.1
        linarith
    _ ≤ M := hsum

/-- **Ball invariance using the source structure.**

Specialization of `duhamel_ball_invariance` where the source bound
`S = M · (a + b · M^α)` comes from `intervalLogisticSource_abs_bound`,
and the initial data bound `H = M/2` with `S · T ≤ M/2`. -/
theorem duhamel_ball_invariance_logistic
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {u : ℝ → intervalDomainPoint → ℝ}
    {M T : ℝ} (hM : 0 < M) (hT : 0 < T)
    (hu₀ : ∀ y, |intervalDomainLift u₀ y| ≤ M / 2)
    (hu : ∀ s y, 0 ≤ s → s ≤ T → |u s y| ≤ M)
    (hST : M * (p.a + p.b * M ^ p.α) * T ≤ M / 2)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint) :
    |intervalDuhamelOperator p u₀ u t x| ≤ M := by
  have hS_nn : 0 ≤ M * (p.a + p.b * M ^ p.α) := by
    apply mul_nonneg hM.le
    have : 0 ≤ p.b * M ^ p.α :=
      mul_nonneg p.hb (Real.rpow_nonneg hM.le _)
    linarith [p.ha]
  apply duhamel_ball_invariance p u₀ hT hM.le (div_nonneg hM.le two_pos.le) hS_nn
    hu₀
  · intro s hs0 hsT y
    exact intervalLogisticSource_lift_abs_bound p hM (fun y' => hu s y' hs0 hsT) y
  · linarith
  · exact ht0
  · exact htT

/-! ### Picard iteration and the Banach fixed-point theorem

We construct the Picard iteration sequence for a general operator `Φ`,
prove the geometric decrease bound, and show that the pointwise limit
is a fixed point.  This is the abstract Banach fixed-point theorem
formulated for function spaces without setting up a complete metric
space structure. -/

/-- The Picard iteration sequence: `u_n = Φ^n(0)`. -/
def picardIteration (Φ : (ℝ → intervalDomainPoint → ℝ) →
    (ℝ → intervalDomainPoint → ℝ)) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun _ _ => 0
  | n + 1 => Φ (picardIteration Φ n)

/-- **Geometric decrease for Picard iteration.**

If `Φ` is q-Lipschitz (meaning `|Φ(u₁) - Φ(u₂)| ≤ q · sup|u₁ - u₂|`
uniformly), then consecutive iterates decrease geometrically:
  `|u_{n+1}(t,x) - u_n(t,x)| ≤ q^n · D₀`
where `D₀ = sup|u₁ - u₀|`. -/
theorem picard_geometric_decrease
    {Φ : (ℝ → intervalDomainPoint → ℝ) → (ℝ → intervalDomainPoint → ℝ)}
    {q D₀ : ℝ} (hq : 0 ≤ q) (hD₀ : 0 ≤ D₀)
    (hcontr : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      (∀ s y, |u₁ s y - u₂ s y| ≤ D) →
      ∀ t x, |Φ u₁ t x - Φ u₂ t x| ≤ q * D)
    (hbase : ∀ t x,
      |picardIteration Φ 1 t x - picardIteration Φ 0 t x| ≤ D₀) :
    ∀ (n : ℕ) (t : ℝ) (x : intervalDomainPoint),
      |picardIteration Φ (n + 1) t x - picardIteration Φ n t x| ≤
        q ^ n * D₀ := by
  intro n
  induction n with
  | zero =>
    intro t x; simp only [zero_add, pow_zero, one_mul]; exact hbase t x
  | succ k ih =>
    intro t x
    change |Φ (picardIteration Φ (k + 1)) t x -
          Φ (picardIteration Φ k) t x| ≤ q ^ (k + 1) * D₀
    have hstep := hcontr _ _ (q ^ k * D₀) (mul_nonneg (pow_nonneg hq k) hD₀) ih t x
    calc |Φ (picardIteration Φ (k + 1)) t x -
          Φ (picardIteration Φ k) t x|
        ≤ q * (q ^ k * D₀) := hstep
      _ = q ^ (k + 1) * D₀ := by ring

/-- Telescoping bound: the partial sum of consecutive differences
bounds the difference between distant iterates. -/
theorem picard_telescope_bound
    {Φ : (ℝ → intervalDomainPoint → ℝ) → (ℝ → intervalDomainPoint → ℝ)}
    {q D₀ : ℝ} (_hq : 0 ≤ q) (_hD₀ : 0 ≤ D₀)
    (hgeom : ∀ (n : ℕ) (t : ℝ) (x : intervalDomainPoint),
      |picardIteration Φ (n + 1) t x - picardIteration Φ n t x| ≤
        q ^ n * D₀) :
    ∀ (n N : ℕ), n ≤ N → ∀ (t : ℝ) (x : intervalDomainPoint),
      |picardIteration Φ N t x - picardIteration Φ n t x| ≤
        D₀ * ∑ k ∈ Finset.range (N - n), q ^ (k + n) := by
  intro n N hN t x
  induction N with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero hN
    subst this; simp
  | succ N ih =>
    by_cases hNn : n ≤ N
    · have hN_step := hgeom N t x
      have hN_prev := ih hNn
      calc |picardIteration Φ (N + 1) t x - picardIteration Φ n t x|
          = |(picardIteration Φ (N + 1) t x - picardIteration Φ N t x) +
             (picardIteration Φ N t x - picardIteration Φ n t x)| := by ring_nf
        _ ≤ |picardIteration Φ (N + 1) t x - picardIteration Φ N t x| +
            |picardIteration Φ N t x - picardIteration Φ n t x| := abs_add_le _ _
        _ ≤ q ^ N * D₀ +
            D₀ * ∑ k ∈ Finset.range (N - n), q ^ (k + n) := by linarith
        _ = D₀ * (q ^ N + ∑ k ∈ Finset.range (N - n), q ^ (k + n)) := by ring
        _ = D₀ * ∑ k ∈ Finset.range (N + 1 - n), q ^ (k + n) := by
            congr 1
            have hNn' : N + 1 - n = (N - n) + 1 := by omega
            rw [hNn', Finset.sum_range_succ]
            have : N - n + n = N := Nat.sub_add_cancel hNn
            rw [this]; ring
    · have : N + 1 = n := by omega
      subst this; simp

/-- Geometric partial sum bound: `Σ_{k=0}^{K-1} q^{k+n} ≤ q^n / (1-q)`. -/
theorem geometric_partial_sum_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n K : ℕ) :
    ∑ k ∈ Finset.range K, q ^ (k + n) ≤ q ^ n / (1 - q) := by
  have h1q : (0 : ℝ) < 1 - q := sub_pos.mpr hq1
  have hq_ne_one : q ≠ 1 := ne_of_lt hq1
  -- Factor out q^n
  calc ∑ k ∈ Finset.range K, q ^ (k + n)
      = q ^ n * ∑ k ∈ Finset.range K, q ^ k := by
        conv_lhs => arg 2; ext k; rw [pow_add, mul_comm]
        rw [← Finset.mul_sum]
    _ = q ^ n * ((q ^ K - 1) / (q - 1)) := by
        rw [geom_sum_eq hq_ne_one]
    _ = q ^ n * ((1 - q ^ K) / (1 - q)) := by
        congr 1
        have : (q ^ K - 1) / (q - 1) = (1 - q ^ K) / (1 - q) := by
          rw [show q ^ K - 1 = -(1 - q ^ K) from by ring,
              show q - 1 = -(1 - q) from by ring, neg_div_neg_eq]
        exact this
    _ ≤ q ^ n * (1 / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 n)
        apply div_le_div_of_nonneg_right _ h1q.le
        linarith [pow_nonneg hq0 K]
    _ = q ^ n / (1 - q) := by ring

/-- Uniform tail bound for Picard iterates: the distance from the
`n`-th iterate to the pointwise limit is at most `D₀ · q^n / (1-q)`,
uniformly over all `(t,x)`. -/
theorem picard_tail_bound
    {Φ : (ℝ → intervalDomainPoint → ℝ) → (ℝ → intervalDomainPoint → ℝ)}
    {q D₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hD₀ : 0 ≤ D₀)
    (hgeom : ∀ (m : ℕ) (t : ℝ) (x : intervalDomainPoint),
      |picardIteration Φ (m + 1) t x - picardIteration Φ m t x| ≤
        q ^ m * D₀)
    (u_star : ℝ → intervalDomainPoint → ℝ)
    (hconv : ∀ t x, Filter.Tendsto
      (fun m => picardIteration Φ m t x) Filter.atTop (nhds (u_star t x)))
    (n : ℕ) (t : ℝ) (x : intervalDomainPoint) :
    |u_star t x - picardIteration Φ n t x| ≤
      D₀ * q ^ n / (1 - q) := by
  -- Pass the telescope bound through the limit
  have htendsdiff : Filter.Tendsto
      (fun N => picardIteration Φ N t x - picardIteration Φ n t x)
      Filter.atTop (nhds (u_star t x - picardIteration Φ n t x)) :=
    ((hconv t x).sub tendsto_const_nhds)
  have habs_tends : Filter.Tendsto
      (fun N => |picardIteration Φ N t x - picardIteration Φ n t x|)
      Filter.atTop (nhds |u_star t x - picardIteration Φ n t x|) :=
    htendsdiff.abs
  -- Each partial distance is bounded
  have hpartial_bound : ∀ N, n ≤ N →
      |picardIteration Φ N t x - picardIteration Φ n t x| ≤
        D₀ * q ^ n / (1 - q) := by
    intro N hN
    calc |picardIteration Φ N t x - picardIteration Φ n t x|
        ≤ D₀ * ∑ k ∈ Finset.range (N - n), q ^ (k + n) :=
          picard_telescope_bound hq0 hD₀ hgeom n N hN t x
      _ ≤ D₀ * (q ^ n / (1 - q)) :=
          mul_le_mul_of_nonneg_left (geometric_partial_sum_le hq0 hq1 n _) hD₀
      _ = D₀ * q ^ n / (1 - q) := by ring
  -- Pass through limit
  exact le_of_tendsto habs_tends
    (Filter.eventually_atTop.mpr ⟨n, fun N hN => hpartial_bound N hN⟩)

/-- Pointwise Cauchy sequence: the Picard iterates form a Cauchy
sequence at each `(t,x)`. -/
theorem picard_pointwise_cauchySeq
    {Φ : (ℝ → intervalDomainPoint → ℝ) → (ℝ → intervalDomainPoint → ℝ)}
    {q D₀ : ℝ} (_hq0 : 0 ≤ q) (hq1 : q < 1) (_hD₀ : 0 ≤ D₀)
    (hgeom : ∀ (n : ℕ) (t : ℝ) (x : intervalDomainPoint),
      |picardIteration Φ (n + 1) t x - picardIteration Φ n t x| ≤
        q ^ n * D₀)
    (t : ℝ) (x : intervalDomainPoint) :
    CauchySeq (fun n => picardIteration Φ n t x) := by
  apply cauchySeq_of_le_geometric q D₀ hq1
  intro n
  rw [dist_eq_norm, Real.norm_eq_abs, ← abs_sub_comm]
  have := hgeom n t x
  linarith

/-- A nonneg quantity bounded by `C · q^n` for all `n` with `0 ≤ q < 1`
must be zero. -/
theorem eq_zero_of_le_geometric_pow
    {a C q : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ n : ℕ, a ≤ C * q ^ n) :
    a = 0 := by
  by_contra hne
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
  -- q^n → 0, so C · q^n → 0
  have : Filter.Tendsto (fun n : ℕ => C * q ^ n) Filter.atTop (nhds 0) := by
    have hqn : Filter.Tendsto (fun n : ℕ => q ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have h1 := hqn.const_mul C
    rw [mul_zero] at h1
    exact h1.congr (fun n => by ring)
  rw [Metric.tendsto_atTop] at this
  obtain ⟨N, hN⟩ := this (a / 2) (half_pos ha_pos)
  have := h N
  have hspec := hN N le_rfl
  rw [Real.dist_eq] at hspec
  have : C * q ^ N < a := by
    have h1 : |C * q ^ N - 0| < a / 2 := hspec
    rw [sub_zero] at h1
    have h2 : (0 : ℝ) ≤ C * q ^ N := mul_nonneg hC (pow_nonneg hq0 N)
    rw [abs_of_nonneg h2] at h1
    linarith
  linarith [h N]

/-- **Banach fixed-point theorem via Picard iteration.**

If `Φ` is q-Lipschitz with `0 ≤ q < 1`, the Picard iterates converge
pointwise to a fixed point of `Φ`. -/
theorem banach_fixed_point_picard
    {Φ : (ℝ → intervalDomainPoint → ℝ) → (ℝ → intervalDomainPoint → ℝ)}
    {q D₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hD₀ : 0 ≤ D₀)
    (hcontr : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      (∀ s y, |u₁ s y - u₂ s y| ≤ D) →
      ∀ t x, |Φ u₁ t x - Φ u₂ t x| ≤ q * D)
    (hbase : ∀ t x,
      |picardIteration Φ 1 t x - picardIteration Φ 0 t x| ≤ D₀) :
    ∃ u_star : ℝ → intervalDomainPoint → ℝ,
      ∀ t x, u_star t x = Φ u_star t x := by
  -- Step 1: geometric decrease
  have hgeom := picard_geometric_decrease hq0 hD₀ hcontr hbase
  -- Step 2: pointwise convergence (ℝ is complete)
  have hcauchy := picard_pointwise_cauchySeq hq0 hq1 hD₀ hgeom
  -- Extract the pointwise limit
  have hconv : ∀ t x, ∃ L,
      Filter.Tendsto (fun n => picardIteration Φ n t x)
        Filter.atTop (nhds L) :=
    fun t x => ⟨_, (hcauchy t x).tendsto_limUnder⟩
  choose u_star hu_star using fun t => fun x => hconv t x
  refine ⟨u_star, ?_⟩
  -- Step 3: the limit is a fixed point
  -- Key: |u*(t,x) - Φ(u*)(t,x)| ≤ 2 · D₀ · q^{n+1} / (1-q) for ALL n.
  -- Since q < 1, the RHS → 0, so the LHS = 0.
  intro t x
  have h1q : (0 : ℝ) < 1 - q := sub_pos.mpr hq1
  -- Uniform tail bound
  have htail := picard_tail_bound hq0 hq1 hD₀ hgeom u_star hu_star
  -- Bound |u* - Φ(u*)| ≤ D₀ · q^{n+1} / (1-q) + q · D₀ · q^n / (1-q)
  --                     = 2 · D₀ · q^{n+1} / (1-q)
  have hfp_bound : ∀ n : ℕ,
      |u_star t x - Φ u_star t x| ≤ 2 * D₀ * q ^ (n + 1) / (1 - q) := by
    intro n
    -- Triangle inequality: |u* - Φ(u*)| ≤ |u* - u_{n+1}| + |u_{n+1} - Φ(u*)|
    have hpicard_succ : picardIteration Φ (n + 1) t x =
        Φ (picardIteration Φ n) t x := rfl
    -- Bound on |Φ(u_n) - Φ(u*)|
    have hdiff_n : ∀ s y,
        |picardIteration Φ n s y - u_star s y| ≤ D₀ * q ^ n / (1 - q) := by
      intro s y; rw [abs_sub_comm]; exact htail n s y
    have hPhicontr : |Φ (picardIteration Φ n) t x - Φ u_star t x| ≤
        q * (D₀ * q ^ n / (1 - q)) :=
      hcontr _ _ _ (by positivity) hdiff_n t x
    calc |u_star t x - Φ u_star t x|
        = |(u_star t x - picardIteration Φ (n + 1) t x) +
           (picardIteration Φ (n + 1) t x - Φ u_star t x)| := by ring_nf
      _ ≤ |u_star t x - picardIteration Φ (n + 1) t x| +
          |picardIteration Φ (n + 1) t x - Φ u_star t x| := abs_add_le _ _
      _ = |u_star t x - picardIteration Φ (n + 1) t x| +
          |Φ (picardIteration Φ n) t x - Φ u_star t x| := by rw [hpicard_succ]
      _ ≤ D₀ * q ^ (n + 1) / (1 - q) + q * (D₀ * q ^ n / (1 - q)) := by
          linarith [htail (n + 1) t x]
      _ = 2 * D₀ * q ^ (n + 1) / (1 - q) := by ring
  -- Since this bound holds for all n and tends to 0, |u* - Φ(u*)| = 0
  have habs_nn : 0 ≤ |u_star t x - Φ u_star t x| := abs_nonneg _
  have hC_nn : 0 ≤ 2 * D₀ / (1 - q) := by positivity
  have hzero : |u_star t x - Φ u_star t x| = 0 := by
    apply eq_zero_of_le_geometric_pow habs_nn (by positivity : 0 ≤ 2 * D₀ * q / (1 - q)) hq0 hq1
    intro n
    calc |u_star t x - Φ u_star t x|
        ≤ 2 * D₀ * q ^ (n + 1) / (1 - q) := hfp_bound n
      _ = 2 * D₀ * q / (1 - q) * q ^ n := by rw [pow_succ]; ring
  linarith [abs_eq_zero.mp hzero]

/-- **Existence of a Duhamel fixed point for small time.**

For the logistic source with Lipschitz constant `L` on a ball of
radius `M`, there exists `T > 0` such that the Duhamel operator
has a fixed point.

This is the main local existence theorem for the mild solution
formulation on the interval domain. The fixed point is the mild
solution `u` satisfying the Duhamel integral equation.

The hypotheses package the contraction property of the Duhamel
operator abstractly. In practice, this contraction follows from
`duhamel_contraction_full` with `q = L · T < 1`. -/
theorem duhamel_mild_solution_exists
    {L : ℝ} (hL : 0 < L)
    -- The operator Φ and its contraction property
    {Φ : (ℝ → intervalDomainPoint → ℝ) → (ℝ → intervalDomainPoint → ℝ)}
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    -- Φ is L·T-contractive for some T with L·T < 1
    {T : ℝ} (hT : 0 < T) (hLT : L * T < 1)
    (hcontr : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      (∀ s y, |u₁ s y - u₂ s y| ≤ D) →
      ∀ t x, |Φ u₁ t x - Φ u₂ t x| ≤ L * T * D)
    (hbase : ∀ t x,
      |picardIteration Φ 1 t x - picardIteration Φ 0 t x| ≤ D₀) :
    ∃ u_star : ℝ → intervalDomainPoint → ℝ,
      ∀ t x, u_star t x = Φ u_star t x := by
  have hq0 : 0 ≤ L * T := mul_nonneg hL.le hT.le
  exact banach_fixed_point_picard hq0 hLT hD₀ hcontr hbase

/-! ### Wiring: Banach FP + RegularityBootstrap → localExistence

The `RegularityBootstrap` predicate captures the genuine PDE properties
needed to upgrade a Duhamel fixed point to a classical solution.
Each field requires real PDE analysis — positivity (comparison principle),
pointwise PDE (regularity of the mild solution), Neumann BC, max principle,
and initial trace. -/

/-- Properties that upgrade a Duhamel fixed point u to a classical solution.
These are genuine PDE results, not formalization scaffolding. -/
def RegularityBootstrap (p : CM2Params) (T : ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∃ v : ℝ → intervalDomainPoint → ℝ,
    (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside → 0 < u t x) ∧
    (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv u t x =
        intervalDomain.laplacian (u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (u t) (v t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α)) ∧
    (∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian (v t) x
        - p.μ * v t x + p.ν * (u t x) ^ p.γ) ∧
    (∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv (u t) x = 0 ∧
      intervalDomain.normalDeriv (v t) x = 0) ∧
    intervalDomainClassicalRegularity T u v ∧
    InitialTrace intervalDomain u₀ u

/-- Banach FP + RegularityBootstrap → IsMildSolutionData. -/
theorem isMildSolutionData_of_fp_and_regularity
    (p : CM2Params) {T : ℝ}
    (u₀ : intervalDomainPoint → ℝ)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hfp : ∀ t x, 0 ≤ t → t ≤ T →
      u t x = intervalDuhamelOperator p u₀ u t x)
    (hreg : RegularityBootstrap p T u₀ u) :
    ∃ v, IsMildSolutionData p T u₀ u v := by
  obtain ⟨v, hpos, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨v, hfp, hpos, hpde_u, hpde_v, hbc, hclassreg, htrace⟩

/-- Full composition: Banach FP + RegularityBootstrap → localExistence.
This is the main bridge theorem. The only remaining gap is constructing
`RegularityBootstrap` for the Duhamel fixed point, which requires
genuine PDE analysis (regularity theory, comparison principle, max
principle). Playbook state ③. -/
theorem localExistence_of_fp_and_regularity
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hfp : ∀ t x, 0 ≤ t → t ≤ T →
      u t x = intervalDuhamelOperator p u₀ u t x)
    (hreg : RegularityBootstrap p T u₀ u) :
    ∃ Tmax > 0, ∃ u' v' : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u' v' ∧
      InitialTrace intervalDomain u₀ u' := by
  obtain ⟨v, hdata⟩ := isMildSolutionData_of_fp_and_regularity p u₀ hfp hreg
  exact localExistence_of_isMildSolutionData p u₀ hu₀ hT hdata

/-- The complete conditional localExistence: for each u₀, if we can
produce a Duhamel fixed point (via Banach) with RegularityBootstrap,
then the full local existence theorem holds. -/
theorem localExistence_from_banach_and_regularity
    (p : CM2Params)
    (hmild : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ T > 0, ∃ u : ℝ → intervalDomainPoint → ℝ,
          (∀ t x, 0 ≤ t → t ≤ T →
            u t x = intervalDuhamelOperator p u₀ u t x) ∧
          RegularityBootstrap p T u₀ u) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨T, hT, u, hfp, hreg⟩ := hmild u₀ hu₀
  exact localExistence_of_fp_and_regularity p u₀ hu₀ hT hfp hreg

/-! ### RegularityBootstrap for spatially-constant solutions

For constant-in-time-and-space solutions u(t,x) = c, all fields of
`RegularityBootstrap` are provable from the existing constant-solution
lemmas: Laplacian, chemotaxis divergence, normal derivative, and time
derivative all vanish for constant functions, the equilibrium reaction
term is zero, positivity is immediate, and the initial trace is trivial. -/

/-- RegularityBootstrap for the positive equilibrium u(t,x) = (a/b)^{1/α}
when a > 0 and b > 0. The companion v is the ellipticV relation. -/
theorem equilibrium_regularityBootstrap
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {T : ℝ} (hT : 0 < T) :
    RegularityBootstrap p T
      (constOnInterval ((p.a / p.b) ^ (1 / p.α)))
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α)) := by
  set c := (p.a / p.b) ^ (1 / p.α) with hc_def
  have hc : 0 < c := equilibrium_pos p ha hb
  refine ⟨fun _ _ => ellipticV p c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Positivity
    exact fun _t _x _ht0 _htT _hx => hc
  · -- u-PDE: timeDeriv u = Δu - χ₀·chemDiv + u(a - bu^α)
    intro t x _ht0 _htT hx
    change deriv (fun _s : ℝ => c) t =
      intervalDomainLaplacian (fun _ => c) x
        - p.χ₀ * intervalDomainChemotaxisDiv p (fun _ => c)
            (fun _ => ellipticV p c) x
        + c * (p.a - p.b * c ^ p.α)
    rw [deriv_const, intervalDomainLaplacian_const_zero c hx,
      intervalDomainChemotaxisDiv_const_zero p c (ellipticV p c) hx,
      equilibrium_reaction_zero p ha hb]
    ring
  · -- v-PDE: 0 = Δv - μv + νu^γ
    intro t x _ht0 _htT hx
    change (0 : ℝ) =
      intervalDomainLaplacian (fun _ => ellipticV p c) x
        - p.μ * ellipticV p c + p.ν * c ^ p.γ
    exact ellipticV_pde p c hc hx
  · -- Neumann BC
    intro t x _ht0 _htT hx
    exact ⟨intervalDomainNormalDeriv_const_zero c hx,
           intervalDomainNormalDeriv_const_zero (ellipticV p c) hx⟩
  · -- Classical regularity
    exact constantInTime_classicalRegularity hc hT p
  · -- Initial trace
    exact constantSolution_initialTrace c

/-- RegularityBootstrap for the zero-reaction constant solution u(t,x) = c
when a = 0 and b = 0. Any c > 0 works. -/
theorem zeroReaction_regularityBootstrap
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0)
    (c : ℝ) (hc : 0 < c)
    {T : ℝ} (hT : 0 < T) :
    RegularityBootstrap p T
      (constOnInterval c)
      (fun _ (_ : intervalDomainPoint) => c) := by
  refine ⟨fun _ _ => ellipticV p c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Positivity
    exact fun _t _x _ht0 _htT _hx => hc
  · -- u-PDE
    intro t x _ht0 _htT hx
    change deriv (fun _s : ℝ => c) t =
      intervalDomainLaplacian (fun _ => c) x
        - p.χ₀ * intervalDomainChemotaxisDiv p (fun _ => c)
            (fun _ => ellipticV p c) x
        + c * (p.a - p.b * c ^ p.α)
    rw [deriv_const, intervalDomainLaplacian_const_zero c hx,
      intervalDomainChemotaxisDiv_const_zero p c (ellipticV p c) hx,
      ha, hb]
    simp
  · -- v-PDE
    intro t x _ht0 _htT hx
    exact ellipticV_pde p c hc hx
  · -- Neumann BC
    intro t x _ht0 _htT hx
    exact ⟨intervalDomainNormalDeriv_const_zero c hx,
           intervalDomainNormalDeriv_const_zero (ellipticV p c) hx⟩
  · -- Classical regularity
    exact constantInTime_classicalRegularity hc hT p
  · -- Initial trace
    exact constantSolution_initialTrace c

/-! ### Local existence for constant initial data via the Banach FP chain

We extract the classical solution and initial trace from the
`RegularityBootstrap` for constant solutions, producing `localExistence`
in the same form as `localExistence_of_fp_and_regularity` but without
requiring the Duhamel fixed-point hypothesis (since for constant
solutions the classical solution is constructed directly).

The key observation is that `RegularityBootstrap` packages exactly the
PDE-side data needed for `IsPaper2ClassicalSolution` plus `InitialTrace`.
For constant initial data where the classical solution is already known,
this provides a complete local existence result that goes through the
regularity bootstrap pathway. -/

/-- RegularityBootstrap directly implies local existence without
requiring the Duhamel fixed-point equation. This is the analogue
of `localExistence_of_fp_and_regularity` for the case where
we have the classical solution but not (yet) the Duhamel FP. -/
theorem localExistence_of_regularityBootstrap
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (_hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u : ℝ → intervalDomainPoint → ℝ}
    (hreg : RegularityBootstrap p T u₀ u) :
    ∃ Tmax > 0, ∃ u' v' : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u' v' ∧
      InitialTrace intervalDomain u₀ u' := by
  obtain ⟨v, hpos, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨T, hT, u, v,
    IsPaper2ClassicalSolution.of_components hT hclassreg hpos hpde_u hpde_v hbc,
    htrace⟩

/-- Local existence for constant initial data (equilibrium, a > 0, b > 0)
via the RegularityBootstrap chain. The solution is u(t,x) = (a/b)^{1/α}
constant in both time and space.

This goes through RegularityBootstrap → IsPaper2ClassicalSolution
rather than the direct construction in
`equilibrium_isPaper2ClassicalSolution`, demonstrating that the
bootstrap chain is complete for constant solutions. -/
theorem equilibrium_localExistence_via_regularity
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    ∃ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ ∧
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u := by
  set c := (p.a / p.b) ^ (1 / p.α)
  have hc : 0 < c := equilibrium_pos p ha hb
  refine ⟨constOnInterval c, constOnInterval_pos hc, ?_⟩
  exact localExistence_of_regularityBootstrap p
    (constOnInterval c) (constOnInterval_pos hc) one_pos
    (equilibrium_regularityBootstrap p ha hb one_pos)

/-- Local existence for constant initial data (zero reaction, a = 0, b = 0)
via the RegularityBootstrap chain. The solution is u(t,x) = 1 constant
in both time and space. -/
theorem zeroReaction_localExistence_via_regularity
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) :
    ∃ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ ∧
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u := by
  refine ⟨constOnInterval 1, constOnInterval_pos one_pos, ?_⟩
  exact localExistence_of_regularityBootstrap p
    (constOnInterval 1) (constOnInterval_pos one_pos) one_pos
    (zeroReaction_regularityBootstrap p ha hb 1 one_pos one_pos)

/-- Combined local existence for constant initial data via the
RegularityBootstrap chain. Covers both (a > 0, b > 0) and
(a = 0, b = 0) parameter regimes.

This theorem demonstrates that the full Banach FP → RegularityBootstrap
→ localExistence pathway is complete for spatially-constant solutions.
The only missing piece for GENERAL initial data is the Duhamel
fixed-point equation (Banach contraction on complete trajectory space),
which for constant data is bypassed because the classical solution is
constructed directly. -/
theorem constantData_localExistence_via_regularity
    (p : CM2Params)
    (h : (0 < p.a ∧ 0 < p.b) ∨ (p.a = 0 ∧ p.b = 0)) :
    ∃ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ ∧
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact equilibrium_localExistence_via_regularity p ha hb
  · exact zeroReaction_localExistence_via_regularity p ha hb

/-! ### Classical regularity for spatially-constant time-decreasing solutions

For u(t,x) = φ(t) with φ positive, continuous, differentiable on (0,T),
and φ'(t) ≤ 0 for all t ∈ (0,T), the sup-norm function
`fun t => intervalDomainSupNorm (fun _ => φ t) = fun t => φ t`
is nonincreasing, so `intervalDomainClassicalRegularity` holds.

This covers spatially-constant ODE solutions starting ABOVE the equilibrium:
when φ(0) > (a/b)^{1/α}, the logistic ODE φ' = φ(a - bφ^α) gives φ' ≤ 0
since a - bφ^α ≤ 0 for φ ≥ (a/b)^{1/α}. -/

/-- The sup-norm function of a spatially-constant positive function
equals the function itself: `fun t => intervalDomainSupNorm (fun _ => φ t) = φ`. -/
lemma supNormFun_eq_of_spatially_constant_pos
    {φ : ℝ → ℝ} (hφ_pos : ∀ t, 0 < φ t) :
    (fun t => intervalDomainSupNorm (fun _ : intervalDomainPoint => φ t)) = φ := by
  ext t
  rw [intervalDomainSupNorm_const, abs_of_pos (hφ_pos t)]

/-- The sup-norm derivative condition on `Set.Ioc 0 t₀` for a positive
decreasing spatially-constant function. -/
lemma supNormDerivNonposOn_Ioc_of_decreasing
    {φ : ℝ → ℝ} {t₀ : ℝ} (_ht₀ : 0 < t₀)
    (hφ_pos : ∀ t, 0 < φ t)
    (hφ_cont : ContinuousOn φ (Set.Ioc 0 t₀))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 t₀))
    (hφ_deriv : ∀ t, t ∈ Set.Ioo 0 t₀ → deriv φ t ≤ 0) :
    IntervalDomainSupNormDerivativeNonposOn
      (fun t (_ : intervalDomainPoint) => φ t) (Set.Ioc 0 t₀) := by
  have hsup_eq := supNormFun_eq_of_spatially_constant_pos hφ_pos
  constructor
  · -- ContinuousOn on Ioc 0 t₀
    show ContinuousOn (fun t => intervalDomainSupNorm
      (fun _ : intervalDomainPoint => φ t)) (Set.Ioc 0 t₀)
    rw [hsup_eq]
    exact hφ_cont
  · -- DifferentiableOn on interior (Ioc 0 t₀) = Ioo 0 t₀
    show DifferentiableOn ℝ (fun t => intervalDomainSupNorm
      (fun _ : intervalDomainPoint => φ t)) (interior (Set.Ioc 0 t₀))
    rw [interior_Ioc, hsup_eq]
    exact hφ_diff
  · -- deriv ≤ 0 on interior (Ioc 0 t₀) = Ioo 0 t₀
    intro t ht
    rw [interior_Ioc] at ht
    show deriv (fun s => intervalDomainSupNorm
      (fun _ : intervalDomainPoint => φ s)) t ≤ 0
    have : (fun s => intervalDomainSupNorm
      (fun _ : intervalDomainPoint => φ s)) = φ := hsup_eq
    rw [this]
    exact hφ_deriv t ht

/-- The sup-norm derivative condition on `Set.Ioo 0 T` for a positive
decreasing spatially-constant function. -/
lemma supNormDerivNonposOn_Ioo_of_decreasing
    {φ : ℝ → ℝ} {T : ℝ} (_hT : 0 < T)
    (hφ_pos : ∀ t, 0 < φ t)
    (hφ_cont : ContinuousOn φ (Set.Ioo 0 T))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 T))
    (hφ_deriv : ∀ t, t ∈ Set.Ioo 0 T → deriv φ t ≤ 0) :
    IntervalDomainSupNormDerivativeNonposOn
      (fun t (_ : intervalDomainPoint) => φ t) (Set.Ioo 0 T) := by
  have hsup_eq := supNormFun_eq_of_spatially_constant_pos hφ_pos
  constructor
  · show ContinuousOn (fun t => intervalDomainSupNorm
      (fun _ : intervalDomainPoint => φ t)) (Set.Ioo 0 T)
    rw [hsup_eq]; exact hφ_cont
  · show DifferentiableOn ℝ (fun t => intervalDomainSupNorm
      (fun _ : intervalDomainPoint => φ t)) (interior (Set.Ioo 0 T))
    rw [interior_Ioo, hsup_eq]; exact hφ_diff
  · intro t ht
    rw [interior_Ioo] at ht
    show deriv (fun s => intervalDomainSupNorm
      (fun _ : intervalDomainPoint => φ s)) t ≤ 0
    rw [hsup_eq]; exact hφ_deriv t ht

/-- A spatially-constant function with positive and non-increasing values
satisfies `intervalDomainClassicalRegularity` for any v.

The key point: the sup-norm function `t ↦ intervalDomainSupNorm (fun _ => φ t)`
equals `t ↦ φ t` (since φ > 0), and its derivative is nonpositive. The
condition `supNorm > equilibrium` in the first conjunct is vacuously or
non-vacuously satisfied — either way, the derivative condition holds. -/
theorem classicalRegularity_of_spatially_constant_decreasing
    {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hφ_pos : ∀ t, 0 < φ t)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 T))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 T))
    (hφ_deriv_nonpos : ∀ t, t ∈ Set.Ioo 0 T → deriv φ t ≤ 0)
    (v : ℝ → intervalDomainPoint → ℝ) :
    intervalDomainClassicalRegularity T
      (fun t (_ : intervalDomainPoint) => φ t) v := by
  unfold intervalDomainClassicalRegularity
  refine ⟨?_, ?_⟩
  · -- First conjunct: for any p' with a > 0, b > 0, if supNorm > equilibrium,
    -- the sup-norm is nonincreasing on Ioc 0 t₀.
    intro _p' _hχ _ha _hb t₀ ht₀ ht₀T _hsup_gt
    apply supNormDerivNonposOn_Ioc_of_decreasing ht₀ hφ_pos
    · exact hφ_cont.mono (Set.Ioc_subset_Icc_self.trans
        (Set.Icc_subset_Icc_right (le_of_lt ht₀T)))
    · exact hφ_diff.mono (fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt ht₀T)⟩)
    · exact fun t ht => hφ_deriv_nonpos t ⟨ht.1, lt_of_lt_of_le ht.2 (le_of_lt ht₀T)⟩
  · -- Second conjunct: for any p' with a = 0, b = 0,
    -- the sup-norm is nonincreasing on Ioo 0 T.
    intro _p' _hχ _ha _hb
    apply supNormDerivNonposOn_Ioo_of_decreasing hT hφ_pos
    · exact hφ_cont.mono Set.Ioo_subset_Icc_self
    · exact hφ_diff
    · exact hφ_deriv_nonpos

/-! ### RegularityBootstrap for above-equilibrium ODE solutions

For a spatially-constant ODE solution u(t,x) = φ(t) where φ solves
φ' = φ(a - bφ^α) with φ(0) = c₀ > (a/b)^{1/α}, we can prove
`RegularityBootstrap` from the following hypotheses on φ:

1. φ is positive on [0,T]
2. φ is continuous on [0,T], differentiable on (0,T)
3. φ'(t) ≤ 0 on (0,T) (decreasing)
4. φ satisfies the ODE: φ'(t) = φ(t)(a - bφ(t)^α)
5. φ(0) = c₀ (initial value)

These are genuine ODE results. The bootstrap then follows by combining:
- PDE reduction: all spatial terms vanish for constant-in-space functions
- Classical regularity: from the decreasing property
- Initial trace: from φ(t) → c₀ as t → 0⁺ -/

/-- RegularityBootstrap for a spatially-constant ODE solution φ that is
positive, continuous, differentiable, decreasing, and solves the logistic ODE.

This is the bridge between ODE analysis (properties of φ) and the PDE
regularity structure needed for `IsPaper2ClassicalSolution`. -/
theorem aboveEquilibrium_regularityBootstrap
    (p : CM2Params) (_ha : 0 < p.a) (_hb : 0 < p.b)
    {T : ℝ} (hT : 0 < T)
    {φ : ℝ → ℝ} (c₀ : ℝ) (_hc₀ : (p.a / p.b) ^ (1 / p.α) ≤ c₀)
    -- ODE solution properties
    (hφ_pos : ∀ t, 0 < φ t)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 T))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 T))
    (hφ_deriv_nonpos : ∀ t, t ∈ Set.Ioo 0 T → deriv φ t ≤ 0)
    -- The ODE equation: φ'(t) = φ(t)(a - bφ(t)^α) at interior points
    (hφ_ode : ∀ t, t ∈ Set.Ioo 0 T →
      deriv φ t = φ t * (p.a - p.b * (φ t) ^ p.α))
    -- Initial value: φ(0) = c₀
    (hφ_init : φ 0 = c₀)
    -- Continuity at 0 (for the initial trace)
    (hφ_cont_at_zero : ContinuousAt φ 0) :
    RegularityBootstrap p T
      (constOnInterval c₀)
      (fun t (_ : intervalDomainPoint) => φ t) := by
  refine ⟨fun t _ => ellipticV p (φ t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Positivity
    exact fun _t _x _ht0 _htT _hx => hφ_pos _
  · -- u-PDE: timeDeriv u = Δu - χ₀·chemDiv + u(a - bu^α)
    intro t x _ht0 _htT hx
    -- u(t,x) = φ(t), so timeDeriv u t x = φ'(t)
    -- Laplacian of constant = 0, chemtaxis div of constant = 0
    change deriv (fun s : ℝ => φ s) t =
      intervalDomainLaplacian (fun _ => φ t) x
        - p.χ₀ * intervalDomainChemotaxisDiv p (fun _ => φ t)
            (fun _ => ellipticV p (φ t)) x
        + φ t * (p.a - p.b * (φ t) ^ p.α)
    rw [intervalDomainLaplacian_const_zero (φ t) hx,
      intervalDomainChemotaxisDiv_const_zero p (φ t) (ellipticV p (φ t)) hx]
    have ht_mem : t ∈ Set.Ioo 0 T := ⟨‹0 < t›, ‹t < T›⟩
    rw [hφ_ode t ht_mem]; ring
  · -- v-PDE: 0 = Δv - μv + νu^γ
    intro t x _ht0 _htT hx
    change (0 : ℝ) =
      intervalDomainLaplacian (fun _ => ellipticV p (φ t)) x
        - p.μ * ellipticV p (φ t) + p.ν * (φ t) ^ p.γ
    exact ellipticV_pde p (φ t) (hφ_pos t) hx
  · -- Neumann BC
    intro t x _ht0 _htT hx
    exact ⟨intervalDomainNormalDeriv_const_zero (φ t) hx,
           intervalDomainNormalDeriv_const_zero (ellipticV p (φ t)) hx⟩
  · -- Classical regularity
    exact classicalRegularity_of_spatially_constant_decreasing hT hφ_pos
      hφ_cont hφ_diff hφ_deriv_nonpos _
  · -- Initial trace: φ(t) → c₀ = φ(0) as t → 0⁺
    intro ε hε
    -- Since φ is continuous at 0, ∃ δ > 0 with |φ(t) - φ(0)| < ε for t ∈ (0,δ)
    rw [Metric.continuousAt_iff] at hφ_cont_at_zero
    obtain ⟨δ, hδ, hball⟩ := hφ_cont_at_zero ε hε
    refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
    change intervalDomainSupNorm (fun x => φ t - constOnInterval c₀ x) < ε
    have hconst : (fun _ : intervalDomainPoint => φ t - c₀) =
        fun x => φ t - constOnInterval c₀ x := by
      ext; simp [constOnInterval]
    rw [← hconst, intervalDomainSupNorm_const]
    rw [abs_sub_comm]
    have : |c₀ - φ t| = |φ 0 - φ t| := by rw [hφ_init]
    rw [this]
    rw [← Real.dist_eq, dist_comm]
    exact hball (by rwa [Real.dist_eq, sub_zero, abs_of_pos ht0])

/-! ### Sup-norm triangle inequality and initial approach for intervalDomain -/

/-- Helper: `intervalDomainSupNorm` is nonneg.  When BddAbove holds, it's the
sup of nonneg values ≥ 0.  When NOT BddAbove, it equals 0 by definition. -/
lemma intervalDomainSupNorm_nonneg (f : intervalDomainPoint → ℝ) :
    0 ≤ intervalDomainSupNorm f := by
  unfold intervalDomainSupNorm
  by_cases hbdd : BddAbove (Set.range (fun x : intervalDomainPoint => |f x|))
  · exact le_csSup_of_le hbdd ⟨⟨0, le_refl 0, zero_le_one⟩, rfl⟩ (abs_nonneg _)
  · show 0 ≤ sSup (Set.range fun x => |f x|)
    rw [Real.sSup_def, dif_neg (by simp [hbdd])]

/-- When NOT BddAbove, `intervalDomainSupNorm` equals 0. -/
private lemma intervalDomainSupNorm_eq_zero_of_not_bddAbove
    {f : intervalDomainPoint → ℝ}
    (h : ¬BddAbove (Set.range (fun x => |f x|))) :
    intervalDomainSupNorm f = 0 := by
  unfold intervalDomainSupNorm
  rw [Real.sSup_def]
  simp only [Set.range_nonempty, h, and_false, ↓reduceDIte]

/-- If BddAbove holds for `range |f|` and `range |g|`, then BddAbove
holds for `range |f - g|`. -/
private lemma bddAbove_range_abs_diff_of_bddAbove
    {f g : intervalDomainPoint → ℝ}
    (hf : BddAbove (Set.range (fun x => |f x|)))
    (hg : BddAbove (Set.range (fun x => |g x|))) :
    BddAbove (Set.range (fun x => |f x - g x|)) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf + Mg, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ Mf + Mg := add_le_add (hMf ⟨x, rfl⟩) (hMg ⟨x, rfl⟩)

/-- **Initial sup-norm approach for intervalDomain.**

For any classical solution with initial trace, `supNorm(u t)` is close to
`supNorm u₀` for small positive time.

**Proof**: From `InitialTrace`, for ε > 0, ∃ δ > 0 with
`supNorm(u t - u₀) < ε` for `t ∈ (0, δ)`.  When BddAbove holds for the
relevant ranges (the mathematically meaningful case), the triangle inequality
`|u t x| ≤ |u₀ x| + |u t x - u₀ x| ≤ supNorm u₀ + ε` gives the result via
`csSup_le`.  When BddAbove fails, `supNorm(u t) = 0 ≤ supNorm u₀ + ε`. -/
theorem initialSupNormApproach_intervalDomain (p : CM2Params)
    (u₀ : intervalDomain.Point → ℝ) (_hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd_u0 : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ T ∧ ∀ t, 0 < t → t < δ →
      intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ + ε := by
  obtain ⟨δ₁, hδ₁_pos, hδ₁_bound⟩ := htrace ε hε
  refine ⟨min δ₁ T, lt_min hδ₁_pos hT, min_le_right _ _, fun t ht0 htδ => ?_⟩
  have ht_lt_δ₁ : t < δ₁ := lt_of_lt_of_le htδ (min_le_left _ _)
  have hsup_diff : intervalDomainSupNorm (fun x => u t x - u₀ x) < ε :=
    hδ₁_bound t ht0 ht_lt_δ₁
  show intervalDomainSupNorm (u t) ≤ intervalDomainSupNorm u₀ + ε
  by_cases hbdd_ut : BddAbove (Set.range (fun x : intervalDomainPoint => |u t x|))
  · -- BddAbove case: triangle inequality
    have hbdd_diff : BddAbove
        (Set.range (fun x : intervalDomainPoint => |u t x - u₀ x|)) := by
      obtain ⟨M1, hM1⟩ := hbdd_ut; obtain ⟨M2, hM2⟩ := hbdd_u0
      exact ⟨M1 + M2, fun _ ⟨x, hx⟩ => hx ▸
        (abs_sub (u t x) (u₀ x)).trans (add_le_add (hM1 ⟨x, rfl⟩) (hM2 ⟨x, rfl⟩))⟩
    unfold intervalDomainSupNorm
    haveI : Nonempty intervalDomainPoint :=
      ⟨⟨0, le_refl _, zero_le_one⟩⟩
    have hne : (Set.range (fun x : intervalDomainPoint => |u t x|)).Nonempty :=
      Set.range_nonempty _
    apply csSup_le hne
    rintro _ ⟨x, rfl⟩
    have hxdiff : |u t x - u₀ x| < ε :=
      lt_of_le_of_lt (le_csSup hbdd_diff ⟨x, rfl⟩) hsup_diff
    calc |u t x| = |u₀ x + (u t x - u₀ x)| := by ring_nf
      _ ≤ |u₀ x| + |u t x - u₀ x| := abs_add_le _ _
      _ ≤ sSup (Set.range (fun x => |u₀ x|)) + |u t x - u₀ x| :=
          add_le_add (le_csSup hbdd_u0 ⟨x, rfl⟩) le_rfl
      _ ≤ sSup (Set.range (fun x => |u₀ x|)) + ε := by linarith
  · -- ¬BddAbove: supNorm(u t) = 0
    rw [intervalDomainSupNorm_eq_zero_of_not_bddAbove hbdd_ut]
    linarith [intervalDomainSupNorm_nonneg u₀]

/-- Local existence for spatially-constant initial data above equilibrium,
via the RegularityBootstrap chain.

Given a CM2Params p with a > 0, b > 0, and a function φ solving the
logistic ODE with initial value c₀ ≥ (a/b)^{1/α}, this produces a
classical solution on intervalDomain. -/
theorem aboveEquilibrium_localExistence
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {T : ℝ} (hT : 0 < T)
    {φ : ℝ → ℝ} (c₀ : ℝ) (hc₀ : (p.a / p.b) ^ (1 / p.α) ≤ c₀)
    (hφ_pos : ∀ t, 0 < φ t)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 T))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 T))
    (hφ_deriv_nonpos : ∀ t, t ∈ Set.Ioo 0 T → deriv φ t ≤ 0)
    (hφ_ode : ∀ t, t ∈ Set.Ioo 0 T →
      deriv φ t = φ t * (p.a - p.b * (φ t) ^ p.α))
    (hφ_init : φ 0 = c₀)
    (hφ_cont_at_zero : ContinuousAt φ 0) :
    ∃ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ ∧
      ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u₀ u := by
  have hc₀_pos : 0 < c₀ :=
    lt_of_lt_of_le (equilibrium_pos p ha hb) hc₀
  refine ⟨constOnInterval c₀, constOnInterval_pos hc₀_pos, ?_⟩
  exact localExistence_of_regularityBootstrap p
    (constOnInterval c₀) (constOnInterval_pos hc₀_pos) hT
    (aboveEquilibrium_regularityBootstrap p ha hb hT c₀ hc₀
      hφ_pos hφ_cont hφ_diff hφ_deriv_nonpos hφ_ode hφ_init hφ_cont_at_zero)

end ShenWork.IntervalDomainExistence

end
