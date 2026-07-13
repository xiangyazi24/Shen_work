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
import ShenWork.Paper2.IntervalDomainChain
import ShenWork.Paper2.IntervalDomainClassicalUniqueness
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.ODEExistence
import ShenWork.PDE.ODEUniqueness

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
  refine ⟨⟨⟨|c|, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩; simp [constOnInterval]
  · exact continuous_const
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

/-- The lift of a constant function agrees with the constant on the open
interior `(0,1)`. -/
lemma intervalDomainLift_const_eqOn_Ioo (c : ℝ) :
    Set.EqOn (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (fun _ => c) (Set.Ioo (0 : ℝ) 1) := by
  intro y hy
  have hy' : y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
  rw [intervalDomainLift_const]
  simp [hy']

/-- The lift of a constant function is `C²` on the open interior `(0,1)`,
because it agrees there with a (globally `C^∞`) constant function. -/
lemma intervalDomainLift_const_contDiffOn (c : ℝ) :
    ContDiffOn ℝ 2 (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (Set.Ioo (0 : ℝ) 1) :=
  (contDiff_const.contDiffOn).congr (intervalDomainLift_const_eqOn_Ioo c)

/-- **Genuine interior-Neumann for a spatially-constant lift.**  The derivative
of the lift of a constant is `0` on the open interior `(0,1)`, so it tends to `0`
along the one-sided endpoint filters `𝓝[>] 0` and `𝓝[<] 1`.  This discharges the
fifth (genuine-Neumann) conjunct of `intervalDomainClassicalRegularity` for any
spatially-constant solution. -/
lemma intervalDomainLift_const_neumann (c : ℝ) :
    Filter.Tendsto (deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  constructor
  · -- On `𝓝[>] 0` the argument eventually lies in `(0,1)`, where deriv = 0.
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨Set.Ioo (0 : ℝ) 1, Ioo_mem_nhdsGT (by norm_num),
      fun y hy => (intervalDomainLift_const_deriv_zero c hy).symm⟩
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨Set.Ioo (0 : ℝ) 1, Ioo_mem_nhdsLT (by norm_num),
      fun y hy => (intervalDomainLift_const_deriv_zero c hy).symm⟩

/-- **Closed-`Icc` spatial `C²` for a constant lift.**  On the *closed* interval
`Icc 0 1` the lift of a constant agrees with the (globally `C^∞`) constant `c`,
so it is `C²` on the closed interval (one-sided derivatives at the endpoints). -/
lemma intervalDomainLift_const_contDiffOn_Icc (c : ℝ) :
    ContDiffOn ℝ 2 (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (Set.Icc (0 : ℝ) 1) := by
  have heq : Set.EqOn (intervalDomainLift (fun _ : intervalDomainPoint => c))
      (fun _ => c) (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    rw [intervalDomainLift_const]
    simp [hy]
  exact (contDiff_const.contDiffOn).congr heq

/-- **Genuine endpoint Neumann values for a constant lift.**  The full (two-sided)
`deriv` of the lift of a constant vanishes at both endpoints `0` and `1`: the lift
`c·𝟙[0,1]` is discontinuous there (jump to `0` outside `[0,1]`), hence not
differentiable, so `deriv = 0` by the Mathlib junk-value convention. -/
lemma intervalDomainLift_const_deriv_endpoint_zero (c : ℝ) :
    deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) 0 = 0 ∧
      deriv (intervalDomainLift (fun _ : intervalDomainPoint => c)) 1 = 0 := by
  constructor
  · by_cases hc : c = 0
    · subst hc
      have : intervalDomainLift (fun _ : intervalDomainPoint => (0 : ℝ))
          = fun _ => 0 := by
        rw [intervalDomainLift_const]; funext x; simp
      rw [this]; exact deriv_const 0 0
    · apply deriv_zero_of_not_differentiableAt
      intro hdiff
      have hcont : ContinuousAt
          (intervalDomainLift (fun _ : intervalDomainPoint => c)) 0 :=
        hdiff.continuousAt
      have hval0 : intervalDomainLift (fun _ : intervalDomainPoint => c) 0 = c := by
        rw [intervalDomainLift_const]; simp
      -- From the left of `0` the lift is `0`; continuity at `0` would force `c = 0`.
      have hlim : Filter.Tendsto
          (intervalDomainLift (fun _ : intervalDomainPoint => c))
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds c) := by
        have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0:ℝ)))
        rwa [hval0] at this
      have hzero : Filter.Tendsto
          (intervalDomainLift (fun _ : intervalDomainPoint => c))
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds 0) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Iio 0, self_mem_nhdsWithin, fun y hy => ?_⟩
        rw [intervalDomainLift_const]
        have : y ∉ Set.Icc (0 : ℝ) 1 := by
          intro hmem; exact absurd hmem.1 (not_le.mpr hy)
        simp [this]
      exact hc (tendsto_nhds_unique hlim hzero)
  · by_cases hc : c = 0
    · subst hc
      have : intervalDomainLift (fun _ : intervalDomainPoint => (0 : ℝ))
          = fun _ => 0 := by
        rw [intervalDomainLift_const]; funext x; simp
      rw [this]; exact deriv_const 1 0
    · apply deriv_zero_of_not_differentiableAt
      intro hdiff
      have hcont : ContinuousAt
          (intervalDomainLift (fun _ : intervalDomainPoint => c)) 1 :=
        hdiff.continuousAt
      have hval1 : intervalDomainLift (fun _ : intervalDomainPoint => c) 1 = c := by
        rw [intervalDomainLift_const]; simp
      have hlim : Filter.Tendsto
          (intervalDomainLift (fun _ : intervalDomainPoint => c))
          (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds c) := by
        have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
        rwa [hval1] at this
      have hzero : Filter.Tendsto
          (intervalDomainLift (fun _ : intervalDomainPoint => c))
          (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 0) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi 1, self_mem_nhdsWithin, fun y hy => ?_⟩
        rw [intervalDomainLift_const]
        have : y ∉ Set.Icc (0 : ℝ) 1 := by
          intro hmem; exact absurd hmem.2 (not_le.mpr hy)
        simp [this]
      exact hc (tendsto_nhds_unique hlim hzero)

/-- **Closed-slab joint `∂ₜ` continuity for a constant-in-time lift.**  When `u`
is constant in time (`u s = u`), the time-derivative field `(t,x) ↦ ∂ₜ(lift (u s))
x = 0` is identically `0`, hence continuous on `Ioo 0 T ×ˢ Icc 0 1`. -/
lemma intervalDomainLift_constInTime_jointDeriv_continuousOn
    {T : ℝ} (g : ℝ → intervalDomainPoint → ℝ)
    (hg : ∀ s s', g s = g s') :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => deriv (fun s : ℝ => intervalDomainLift (g s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have h0 : (Function.uncurry
      (fun (t : ℝ) (x : ℝ) =>
        deriv (fun s : ℝ => intervalDomainLift (g s) x) t)) = fun _ => (0 : ℝ) := by
    funext q
    have hconst : (fun s : ℝ => intervalDomainLift (g s) q.2)
        = fun _ => intervalDomainLift (g q.1) q.2 := by
      funext s; rw [hg s q.1]
    simp only [Function.uncurry]
    rw [hconst]; exact deriv_const _ _
  rw [h0]; exact continuousOn_const

/-- **(R1) CLOSED-slab joint continuity of the SOLUTION field for a
constant-in-time, constant-in-space lift.**  When `g s ≡ (fun _ => c)`, the
solution field `(t,x) ↦ intervalDomainLift (g t) x` restricted to the slab
`Ioo 0 T ×ˢ Icc 0 1` equals the constant `c` (the lift is `c` on `[0,1]`), hence
is jointly continuous.  This discharges conjunct (9) for the build-path
constructors. -/
lemma intervalDomainLift_constInTimeSpace_field_continuousOn
    {T : ℝ} (c : ℝ) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          intervalDomainLift ((fun _s (_ : intervalDomainPoint) => c) t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
  -- On the slab the spatial argument lies in `[0,1]`, where the constant lift
  -- equals `c`; so the field equals the constant `c` there.
  refine ContinuousOn.congr (continuousOn_const (c := c)) ?_
  intro q hq
  obtain ⟨_, hx⟩ := hq
  simp only [Function.uncurry]
  rw [intervalDomainLift_const]
  simp [hx]

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
    intervalDomainNormalDeriv (fun _ : intervalDomainPoint => c) x = 0 := by
  have hx' : x.1 = 0 ∨ x.1 = 1 := by simpa [intervalDomain] using hx
  exact intervalDomainNormalDeriv_const_endpoint_zero c hx'

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) spatial C² regularity on (0,1).  Both `u ≡ c` and
    -- `v ≡ ellipticV p c` are constant in space, so their lifts are C² there.
    intro _t _ht
    exact ⟨intervalDomainLift_const_contDiffOn c,
           intervalDomainLift_const_contDiffOn (ellipticV p c)⟩
  · -- Fourth conjunct: interior time `C¹`.  Both slices are constant in time,
    -- hence trivially differentiable in `t`, and their time derivatives are the
    -- constant function `0` (via `deriv_const`), which is continuous on `(0,T)`.
    intro _x _t _ht
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact differentiableAt_const c
    · exact differentiableAt_const (ellipticV p c)
    · have h0 : (fun s : ℝ => deriv (fun _r : ℝ => c) s) = fun _ => (0 : ℝ) := by
        funext s; exact deriv_const s c
      rw [h0]; exact continuousOn_const
    · have h0 : (fun s : ℝ => deriv (fun _r : ℝ => ellipticV p c) s)
          = fun _ => (0 : ℝ) := by
        funext s; exact deriv_const s (ellipticV p c)
      rw [h0]; exact continuousOn_const
  · -- Fifth conjunct: JOINT space-time continuity of `∂ₜ`.  Both `u ≡ c` and
    -- `v ≡ ellipticV p c` are constant in time, so the lift is constant in `s`
    -- and `∂ₜ ≡ 0` as a function of `(t,x)`, which is (jointly) continuous.
    constructor
    · have h0 : (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift
              ((fun _s (_ : intervalDomainPoint) => c) s) x) t))
          = fun _ => (0 : ℝ) := by
        funext q; simp [Function.uncurry, deriv_const]
      rw [h0]; exact continuousOn_const
    · have h0 : (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ => intervalDomainLift
              ((fun _s (_ : intervalDomainPoint) => ellipticV p c) s) x) t))
          = fun _ => (0 : ℝ) := by
        funext q; simp [Function.uncurry, deriv_const]
      rw [h0]; exact continuousOn_const
  · -- Sixth conjunct: genuine interior-Neumann.  Both `u ≡ c` and
    -- `v ≡ ellipticV p c` are spatially constant, so their lift derivatives
    -- vanish on `(0,1)` and tend to `0` at both endpoints.
    intro _t _ht
    exact ⟨intervalDomainLift_const_neumann c,
           intervalDomainLift_const_neumann (ellipticV p c)⟩
  · -- Seventh conjunct: CLOSED-`Icc` spatial `C²` + genuine endpoint Neumann.
    intro _t _ht
    exact ⟨⟨intervalDomainLift_const_contDiffOn_Icc c,
            (intervalDomainLift_const_deriv_endpoint_zero c).1,
            (intervalDomainLift_const_deriv_endpoint_zero c).2⟩,
           ⟨intervalDomainLift_const_contDiffOn_Icc (ellipticV p c),
            (intervalDomainLift_const_deriv_endpoint_zero (ellipticV p c)).1,
            (intervalDomainLift_const_deriv_endpoint_zero (ellipticV p c)).2⟩⟩
  · -- Eighth conjunct: CLOSED-slab joint `∂ₜ` continuity (constant in time).
    exact ⟨intervalDomainLift_constInTime_jointDeriv_continuousOn
            (fun _ (_ : intervalDomainPoint) => c) (fun _ _ => rfl),
           intervalDomainLift_constInTime_jointDeriv_continuousOn
            (fun _ (_ : intervalDomainPoint) => ellipticV p c) (fun _ _ => rfl)⟩
  · -- Ninth conjunct (R1): CLOSED-slab joint continuity of the SOLUTION field.
    -- Constant in time and space, so the lift equals `c` (resp. `ellipticV p c`)
    -- on the slab, hence jointly continuous.
    exact ⟨intervalDomainLift_constInTimeSpace_field_continuousOn c,
           intervalDomainLift_constInTimeSpace_field_continuousOn (ellipticV p c)⟩

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
    (fun _t _x _ht0 _htT => hc)
    -- v-nonnegativity (chemical concentration ≥ 0)
    (fun _t _x _ht0 _htT => (ellipticV_pos p hc).le)
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
    (fun _t _x _ht0 _htT => hc)
    (fun _t _x _ht0 _htT => (ellipticV_pos p hc).le)
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
  -- Positivity of u on the CLOSED domain (positive classical solution; the
  -- strong maximum principle forces `u > 0` up to the Neumann boundary).
  (∀ t x, 0 < t → t < T → 0 < u t x) ∧
  -- Nonnegativity of the chemical concentration `v` on the CLOSED domain
  -- (positive classical solution: `u > 0`, `v ≥ 0`).
  (∀ t x, 0 < t → t < T → 0 ≤ v t x) ∧
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
      hdata.2.2.2.2.2.2.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
      hdata.2.2.2.2.2.1,
    hdata.2.2.2.2.2.2.2⟩

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

/-! ### Picard base step for bounded initial data

The concrete Picard construction below needs a bound on the first increment
`Φ(0) - 0`.  For the interval Duhamel operator this follows directly from
the `L∞` contraction of the interval heat helper: the logistic source of the
zero trajectory is identically zero, so the first Picard step is just the
semigroup applied to the initial datum. -/

@[simp] theorem neumannHeatKernel_zerothReflection_zero_time
    (L x y : ℝ) :
    neumannHeatKernel_zerothReflection L 0 x y = 0 := by
  simp [neumannHeatKernel_zerothReflection, heatKernel_zero]

@[simp] theorem normalizedZerothReflectionKernel_zero_time
    (L x y : ℝ) :
    normalizedZerothReflectionKernel L 0 x y = 0 := by
  simp [normalizedZerothReflectionKernel]

@[simp] theorem intervalSemigroupOperator_zero_time
    (L : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalSemigroupOperator L 0 f x = 0 := by
  simp [intervalSemigroupOperator]

@[simp] theorem intervalLogisticSource_zero
    (p : CM2Params) (x : intervalDomainPoint) :
    intervalLogisticSource p (fun _ : intervalDomainPoint => 0) x = 0 := by
  simp [intervalLogisticSource]

@[simp] theorem intervalDomainLift_zero :
    intervalDomainLift (fun _ : intervalDomainPoint => 0) = fun _ : ℝ => 0 := by
  ext x
  simp [intervalDomainLift]

/-- The interval Duhamel operator applied to the zero trajectory has no
Duhamel source term. -/
theorem intervalDuhamelOperator_zero_trajectory
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) :
    intervalDuhamelOperator p u₀ (fun _ _ => 0) t x =
      intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1 := by
  unfold intervalDuhamelOperator
  have hsource :
      (fun s : ℝ =>
        intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalLogisticSource p (fun _ => 0))) x.1)
        = fun _ : ℝ => 0 := by
    funext s
    have hsrc :
        intervalDomainLift (intervalLogisticSource p (fun _ => 0)) =
          fun _ : ℝ => 0 := by
      ext y
      simp [intervalDomainLift]
    rw [hsrc]
    exact intervalSemigroupOperator_zero 1 (t - s) x.1
  rw [hsource]
  simp

/-- Bounded initial data bounds the first Picard step `Φ(0)` on `[0,T]`.

This discharges the concrete `hbase` input of
`intervalDuhamel_fixed_point_exists_of_contraction`; the remaining contraction
input still has to be supplied on a bounded trajectory ball, not on arbitrary
trajectories. -/
theorem intervalDuhamel_zero_trajectory_bound_of_lift_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {H T : ℝ} (hH : 0 ≤ H)
    (hu₀ : ∀ y : ℝ, |intervalDomainLift u₀ y| ≤ H) :
    ∀ t x, 0 ≤ t → t ≤ T →
      |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ H := by
  intro t x ht0 _htT
  rw [intervalDuhamelOperator_zero_trajectory]
  by_cases ht : t = 0
  · subst ht
    simp [hH]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    exact intervalSemigroupOperator_Linfty_bound ht_pos hH hu₀ x.1

/-- Pointwise bounded initial data on the interval gives the Picard base-step
bound used by the local Duhamel fixed-point construction. -/
theorem intervalDuhamel_zero_trajectory_bound_of_initial_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {H T : ℝ} (hH : 0 ≤ H)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H) :
    ∀ t x, 0 ≤ t → t ≤ T →
      |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ H :=
  intervalDuhamel_zero_trajectory_bound_of_lift_bound p u₀ hH
    (intervalDomainLift_abs_le hH hu₀)

/-! ### Coupled parabolic-elliptic mild formulation

The logistic-only `intervalDuhamelOperator` above is not the full
chemotaxis-elliptic equation used by `IsPaper2ClassicalSolution`.  The
definitions in this section use the full formal source currently present in
`intervalDomain.chemotaxisDiv`:

`-χ₀ * div(u ∇v / (1+v)^β) + u(a - b u^α)`.

For a parabolic-elliptic system the signal is instantaneously determined by
an elliptic resolver `R`, so the coupled fixed point can be written as a fixed
point for `u` alone with `v(t) = R (u(t))`.  The missing analytic object is the
concrete interval Neumann elliptic resolver and its Lipschitz/smoothing
estimates; the Banach wiring below is independent of that construction. -/

/-- Full chemotaxis-logistic source matching the current formal Paper 2
`IsPaper2ClassicalSolution` equation on `intervalDomain`. -/
def intervalCoupledSource (p : CM2Params)
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) : ℝ :=
  -p.χ₀ * intervalDomainChemotaxisDiv p u v x + intervalLogisticSource p u x

/-- Full Duhamel operator with an explicit signal trajectory `v`. -/
def intervalFullDuhamelOperator (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1 +
    ∫ s in Set.Icc 0 t,
      intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1

/-- Coupled parabolic-elliptic Duhamel operator after substituting the
elliptic resolver `v = R u`. -/
def intervalCoupledDuhamelOperator (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullDuhamelOperator p u₀ u (fun s => R (u s)) t x

/-- Sup-norm ball for interval-domain time trajectories on `[0,T]`. -/
def intervalTrajectoryBoundedOn (T M : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → |u t x| ≤ M

@[simp] theorem intervalDomainChemotaxisDiv_zero_left
    (p : CM2Params) (v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalDomainChemotaxisDiv p (fun _ : intervalDomainPoint => 0) v x = 0 := by
  unfold intervalDomainChemotaxisDiv
  have hzero :
      (fun y : ℝ =>
        intervalDomainLift (fun _ : intervalDomainPoint => 0) y *
          deriv (intervalDomainLift v) y /
            (1 + intervalDomainLift v y) ^ p.β) = fun _ : ℝ => 0 := by
    funext y
    simp [intervalDomainLift]
  rw [hzero]
  exact deriv_const x.1 0

@[simp] theorem intervalCoupledSource_zero_left
    (p : CM2Params) (v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalCoupledSource p (fun _ : intervalDomainPoint => 0) v x = 0 := by
  simp [intervalCoupledSource, intervalLogisticSource]

/-- The full coupled Duhamel operator has the same first Picard step as the
logistic-only operator: when `u = 0`, both the logistic source and the
chemotaxis source vanish. -/
theorem intervalFullDuhamelOperator_zero_trajectory
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (v : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) :
    intervalFullDuhamelOperator p u₀ (fun _ _ => 0) v t x =
      intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1 := by
  unfold intervalFullDuhamelOperator
  have hsource :
      (fun s : ℝ =>
        intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift
            (intervalCoupledSource p (fun _ : intervalDomainPoint => 0) (v s)))
          x.1) = fun _ : ℝ => 0 := by
    funext s
    have hsrc :
        intervalDomainLift
            (intervalCoupledSource p (fun _ : intervalDomainPoint => 0) (v s)) =
          fun _ : ℝ => 0 := by
      ext y
      simp [intervalDomainLift]
    rw [hsrc]
    exact intervalSemigroupOperator_zero 1 (t - s) x.1
  rw [hsource]
  simp

theorem intervalCoupledDuhamelOperator_zero_trajectory
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) :
    intervalCoupledDuhamelOperator p R u₀ (fun _ _ => 0) t x =
      intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1 := by
  exact intervalFullDuhamelOperator_zero_trajectory p u₀
    (fun _ => R (fun _ : intervalDomainPoint => 0)) t x

/-- Bounded initial data bounds the first Picard step of the full coupled
Duhamel map. -/
theorem intervalCoupledDuhamel_zero_trajectory_bound_of_initial_bound
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {H T : ℝ} (hH : 0 ≤ H)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H) :
    ∀ t x, 0 ≤ t → t ≤ T →
      |intervalCoupledDuhamelOperator p R u₀ (fun _ _ => 0) t x| ≤ H := by
  intro t x ht0 htT
  rw [intervalCoupledDuhamelOperator_zero_trajectory]
  by_cases ht : t = 0
  · subst ht
    simp [hH]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    exact intervalSemigroupOperator_Linfty_bound ht_pos hH
      (intervalDomainLift_abs_le hH hu₀) x.1

/-- A pointwise source bound gives a pointwise bound for the full Duhamel
operator on `[0,T]`.  This is the map-to-ball half of the local fixed-point
argument. -/
theorem intervalFullDuhamelOperator_bound_of_source_bound
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ)
    {H C T : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u s) (v s)) y| ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (_hint : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (_hlift_int : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u s) (v s)))
        (intervalMeasure 1)) :
    |intervalFullDuhamelOperator p u₀ u v t x| ≤ H + C * T := by
  unfold intervalFullDuhamelOperator
  have hinit :
      |intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1| ≤ H := by
    by_cases ht : t = 0
    · subst ht
      rw [intervalSemigroupOperator_zero_time]
      simpa using hH
    · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      exact intervalSemigroupOperator_Linfty_bound ht_pos hH
        (intervalDomainLift_abs_le hH hu₀) x.1
  have hint_bound :
      |∫ s in Set.Icc (0 : ℝ) t,
        intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1| ≤
          C * T := by
    have hae_bound : ∀ᵐ s ∂MeasureTheory.volume,
        s ∈ Set.Icc (0 : ℝ) t →
          ‖intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1‖ ≤ C := by
      have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          s ≠ t := by
        simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
      filter_upwards [hne] with s hs_ne hs_mem
      rw [Real.norm_eq_abs]
      have hs0 : 0 ≤ s := hs_mem.1
      have hsT : s ≤ T := le_trans hs_mem.2 htT
      have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
      exact intervalSemigroupOperator_Linfty_bound hts_pos hC
        (hsource s hs0 hsT) x.1
    have hvol_fin : MeasureTheory.volume (Set.Icc (0 : ℝ) t) < ⊤ :=
      measure_Icc_lt_top
    have hstep : ‖∫ s in Set.Icc (0 : ℝ) t,
        intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1‖ ≤
          C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' hvol_fin hae_bound
    have hvol_eq : MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) = t := by
      simp [MeasureTheory.Measure.real, Real.volume_Icc, ht0]
    calc |∫ s in Set.Icc (0 : ℝ) t,
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1|
        = ‖∫ s in Set.Icc (0 : ℝ) t,
            intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) := hstep
      _ = C * t := by rw [hvol_eq]
      _ ≤ C * T := mul_le_mul_of_nonneg_left htT hC
  calc
    |intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1 +
        ∫ s in Set.Icc (0 : ℝ) t,
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1|
        ≤ |intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1| +
          |∫ s in Set.Icc (0 : ℝ) t,
            intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (v s))) x.1| :=
          abs_add_le _ _
    _ ≤ H + C * T := add_le_add hinit hint_bound

/-- Source-bound form specialized to the elliptic-resolver coupled Duhamel
operator. -/
theorem intervalCoupledDuhamelOperator_bound_of_source_bound
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {H C T : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hu₀ : ∀ y : intervalDomainPoint, |u₀ y| ≤ H)
    (hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u s) (R (u s))) y| ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (hint : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
        (intervalMeasure 1)) :
    |intervalCoupledDuhamelOperator p R u₀ u t x| ≤ H + C * T :=
  intervalFullDuhamelOperator_bound_of_source_bound p u₀ u (fun s => R (u s))
    hH hC hu₀ hsource ht0 htT x hint hlift_int

/-- Full-source difference bound from a pointwise source bound.  This is the
semigroup part of the coupled contraction proof. -/
theorem intervalFullDuhamelOperator_diff_bound_of_source_bound
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ)
    {C T : ℝ} (_hT : 0 < T) (hC : 0 ≤ C)
    (hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u₁ s) (v₁ s)) y -
       intervalDomainLift (intervalCoupledSource p (u₂ s) (v₂ s)) y| ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (hint₁ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u₁ s) (v₁ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hint₂ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u₂ s) (v₂ s))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int₁ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u₁ s) (v₁ s)))
        (intervalMeasure 1))
    (hlift_int₂ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u₂ s) (v₂ s)))
        (intervalMeasure 1)) :
    |intervalFullDuhamelOperator p u₀ u₁ v₁ t x -
      intervalFullDuhamelOperator p u₀ u₂ v₂ t x| ≤ C * T := by
  unfold intervalFullDuhamelOperator
  simp only [add_sub_add_left_eq_sub]
  rw [← MeasureTheory.integral_sub hint₁ hint₂]
  have hae_bound : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.Icc (0 : ℝ) t →
        ‖(intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalCoupledSource p (u₁ s) (v₁ s))) x.1 -
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalCoupledSource p (u₂ s) (v₂ s))) x.1)‖
          ≤ C := by
    have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        s ≠ t := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Real.norm_eq_abs]
    have hs0 : 0 ≤ s := hs_mem.1
    have hsT : s ≤ T := le_trans hs_mem.2 htT
    have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
    exact intervalSemigroupOperator_contraction hts_pos hC
      (hlift_int₁ s hs0 hsT) (hlift_int₂ s hs0 hsT)
      (hsource s hs0 hsT) x.1
  have hvol_fin : MeasureTheory.volume (Set.Icc (0 : ℝ) t) < ⊤ :=
    measure_Icc_lt_top
  have hstep : ‖∫ s in Set.Icc (0 : ℝ) t,
      (intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalCoupledSource p (u₁ s) (v₁ s))) x.1 -
        intervalSemigroupOperator 1 (t - s)
          (intervalDomainLift (intervalCoupledSource p (u₂ s) (v₂ s))) x.1)‖ ≤
        C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae' hvol_fin hae_bound
  have hvol_eq : MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) = t := by
    simp [MeasureTheory.Measure.real, Real.volume_Icc, ht0]
  calc |∫ s in Set.Icc (0 : ℝ) t,
        (intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalCoupledSource p (u₁ s) (v₁ s))) x.1 -
          intervalSemigroupOperator 1 (t - s)
            (intervalDomainLift (intervalCoupledSource p (u₂ s) (v₂ s))) x.1)|
      = ‖∫ s in Set.Icc (0 : ℝ) t,
          (intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u₁ s) (v₁ s))) x.1 -
            intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u₂ s) (v₂ s))) x.1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ C * MeasureTheory.volume.real (Set.Icc (0 : ℝ) t) := hstep
    _ = C * t := by rw [hvol_eq]
    _ ≤ C * T := mul_le_mul_of_nonneg_left htT hC

/-- Lifted full-source bound from a logistic Lipschitz estimate plus a
chemotaxis-divergence Lipschitz estimate.  The next analytic task is exactly to
derive `hchem` from the concrete Neumann elliptic resolver and heat/GN
smoothing estimates. -/
theorem intervalCoupledSource_lift_diff_bound
    (p : CM2Params) {M L K D : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    {u₁ u₂ v₁ v₂ : intervalDomainPoint → ℝ}
    (hu₁ : ∀ y, |u₁ y| ≤ M) (hu₂ : ∀ y, |u₂ y| ≤ M)
    (hdiff : ∀ y, |u₁ y - u₂ y| ≤ D)
    (hchem : ∀ y,
      |intervalDomainChemotaxisDiv p u₁ v₁ y -
        intervalDomainChemotaxisDiv p u₂ v₂ y| ≤ K * D) :
    ∀ x : ℝ,
      |intervalDomainLift (intervalCoupledSource p u₁ v₁) x -
        intervalDomainLift (intervalCoupledSource p u₂ v₂) x| ≤
          (|p.χ₀| * K + L) * D := by
  have hC : 0 ≤ (|p.χ₀| * K + L) * D := by
    exact mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hK) hL) hD
  apply intervalDomainLift_diff_abs_le hC
  intro y
  unfold intervalCoupledSource
  have hlog :
      |intervalLogisticSource p u₁ y - intervalLogisticSource p u₂ y| ≤
        L * D := by
    calc |intervalLogisticSource p u₁ y - intervalLogisticSource p u₂ y|
        ≤ L * |u₁ y - u₂ y| :=
          intervalLogisticSource_pointwise_lipschitz p hL_lip hu₁ hu₂ y
      _ ≤ L * D := mul_le_mul_of_nonneg_left (hdiff y) hL
  have hchem_scaled :
      |(-p.χ₀ * intervalDomainChemotaxisDiv p u₁ v₁ y) -
        (-p.χ₀ * intervalDomainChemotaxisDiv p u₂ v₂ y)| ≤
          |p.χ₀| * (K * D) := by
    calc
      |(-p.χ₀ * intervalDomainChemotaxisDiv p u₁ v₁ y) -
          (-p.χ₀ * intervalDomainChemotaxisDiv p u₂ v₂ y)|
        = |(-p.χ₀) *
            (intervalDomainChemotaxisDiv p u₁ v₁ y -
              intervalDomainChemotaxisDiv p u₂ v₂ y)| := by ring_nf
      _ = |p.χ₀| *
          |intervalDomainChemotaxisDiv p u₁ v₁ y -
            intervalDomainChemotaxisDiv p u₂ v₂ y| := by
            rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| * (K * D) :=
            mul_le_mul_of_nonneg_left (hchem y) (abs_nonneg _)
  calc
    |(-p.χ₀ * intervalDomainChemotaxisDiv p u₁ v₁ y +
          intervalLogisticSource p u₁ y) -
        (-p.χ₀ * intervalDomainChemotaxisDiv p u₂ v₂ y +
          intervalLogisticSource p u₂ y)|
      = |((-p.χ₀ * intervalDomainChemotaxisDiv p u₁ v₁ y) -
            (-p.χ₀ * intervalDomainChemotaxisDiv p u₂ v₂ y)) +
          (intervalLogisticSource p u₁ y - intervalLogisticSource p u₂ y)| := by
          ring_nf
    _ ≤ |(-p.χ₀ * intervalDomainChemotaxisDiv p u₁ v₁ y) -
            (-p.χ₀ * intervalDomainChemotaxisDiv p u₂ v₂ y)| +
          |intervalLogisticSource p u₁ y - intervalLogisticSource p u₂ y| :=
          abs_add_le _ _
    _ ≤ |p.χ₀| * (K * D) + L * D := add_le_add hchem_scaled hlog
    _ = (|p.χ₀| * K + L) * D := by ring

/-- Coupled-source semigroup contraction after substituting the elliptic
resolver `R`. -/
theorem intervalCoupledDuhamelOperator_diff_bound_of_source_bound
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u₁ u₂ : ℝ → intervalDomainPoint → ℝ)
    {C T : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u₁ s) (R (u₁ s))) y -
       intervalDomainLift (intervalCoupledSource p (u₂ s) (R (u₂ s))) y| ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (hint₁ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u₁ s) (R (u₁ s)))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hint₂ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u₂ s) (R (u₂ s)))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int₁ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u₁ s) (R (u₁ s))))
        (intervalMeasure 1))
    (hlift_int₂ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u₂ s) (R (u₂ s))))
        (intervalMeasure 1)) :
    |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
      intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ C * T := by
  exact intervalFullDuhamelOperator_diff_bound_of_source_bound p u₀ u₁
    (fun s => R (u₁ s)) u₂ (fun s => R (u₂ s)) hT hC hsource ht0 htT x
    hint₁ hint₂ hlift_int₁ hlift_int₂

/-- Coupled Duhamel contraction bound from a logistic Lipschitz estimate and
a chemotaxis-divergence Lipschitz estimate for the elliptic resolver.

This is the last purely semigroup/algebraic step before the genuine elliptic
frontier: constructing an interval Neumann resolver `R` that proves `hchem`
and supplies the listed integrability hypotheses. -/
theorem intervalCoupledDuhamelOperator_diff_bound_of_resolver_chemotaxis_bound
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u₁ u₂ : ℝ → intervalDomainPoint → ℝ)
    {M L K D T : ℝ} (hT : 0 < T)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    (hu₁ : ∀ s y, 0 ≤ s → s ≤ T → |u₁ s y| ≤ M)
    (hu₂ : ∀ s y, 0 ≤ s → s ≤ T → |u₂ s y| ≤ M)
    (hdiff : ∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D)
    (hchem : ∀ s y, 0 ≤ s → s ≤ T →
      |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
        intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y| ≤ K * D)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    (hint₁ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u₁ s) (R (u₁ s)))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hint₂ : MeasureTheory.IntegrableOn
      (fun s => intervalSemigroupOperator 1 (t - s)
        (intervalDomainLift (intervalCoupledSource p (u₂ s) (R (u₂ s)))) x.1)
      (Set.Icc 0 t) MeasureTheory.volume)
    (hlift_int₁ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u₁ s) (R (u₁ s))))
        (intervalMeasure 1))
    (hlift_int₂ : ∀ s, 0 ≤ s → s ≤ T →
      MeasureTheory.Integrable
        (intervalDomainLift (intervalCoupledSource p (u₂ s) (R (u₂ s))))
        (intervalMeasure 1)) :
    |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
      intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤
        (|p.χ₀| * K + L) * T * D := by
  have hC : 0 ≤ (|p.χ₀| * K + L) * D := by
    exact mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hK) hL) hD
  have hsource : ∀ s, 0 ≤ s → s ≤ T → ∀ y,
      |intervalDomainLift (intervalCoupledSource p (u₁ s) (R (u₁ s))) y -
       intervalDomainLift (intervalCoupledSource p (u₂ s) (R (u₂ s))) y| ≤
          (|p.χ₀| * K + L) * D := by
    intro s hs0 hsT
    exact intervalCoupledSource_lift_diff_bound p hL hK hD hL_lip
      (fun y => hu₁ s y hs0 hsT)
      (fun y => hu₂ s y hs0 hsT)
      (fun y => hdiff s y hs0 hsT)
      (fun y => hchem s y hs0 hsT)
  calc
    |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
        intervalCoupledDuhamelOperator p R u₀ u₂ t x|
        ≤ ((|p.χ₀| * K + L) * D) * T :=
          intervalCoupledDuhamelOperator_diff_bound_of_source_bound
            p R u₀ u₁ u₂ hT hC hsource ht0 htT x
            hint₁ hint₂ hlift_int₁ hlift_int₂
    _ = (|p.χ₀| * K + L) * T * D := by ring

/-- The concrete estimates needed from the interval Neumann elliptic resolver
on a fixed trajectory ball.

This is a transparent interface for the resolver file under construction.  It
does not assert existence of `R`; it records exactly the estimates that let the
coupled Duhamel map use the existing heat-semigroup contraction proof. -/
def IntervalCoupledResolverBallEstimates
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (T M K : ℝ) : Prop :=
  (∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u t x| ≤ M) ∧
  (∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      intervalTrajectoryBoundedOn T M u₁ →
      intervalTrajectoryBoundedOn T M u₂ →
      (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ (s : ℝ) (y : intervalDomainPoint), 0 ≤ s → s ≤ T →
          |intervalDomainChemotaxisDiv p (u₁ s) (R (u₁ s)) y -
            intervalDomainChemotaxisDiv p (u₂ s) (R (u₂ s)) y| ≤ K * D) ∧
  (∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ (t : ℝ) (x : intervalDomainPoint), 0 ≤ t → t ≤ T →
          MeasureTheory.IntegrableOn
            (fun s => intervalSemigroupOperator 1 (t - s)
              (intervalDomainLift (intervalCoupledSource p (u s) (R (u s)))) x.1)
            (Set.Icc 0 t) MeasureTheory.volume) ∧
  (∀ u : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u →
        ∀ s, 0 ≤ s → s ≤ T →
          MeasureTheory.Integrable
            (intervalDomainLift (intervalCoupledSource p (u s) (R (u s))))
            (intervalMeasure 1))

/-- Resolver ball estimates discharge the coupled Duhamel contraction on the
trajectory ball.  The constant `A` can be any declared Lipschitz constant above
the explicit algebraic value `|χ₀| K + L`. -/
theorem intervalCoupledDuhamel_closedBall_contraction_of_resolver_estimates
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {T M K L A : ℝ} (hT : 0 < T)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hA_bound : |p.χ₀| * K + L ≤ A)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    (hest : IntervalCoupledResolverBallEstimates p R u₀ T M K) :
    ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      intervalTrajectoryBoundedOn T M u₁ →
      intervalTrajectoryBoundedOn T M u₂ →
      (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ A * T * D := by
  rcases hest with ⟨_hmap, hchem, hint, hlift_int⟩
  intro u₁ u₂ D hD hu₁ hu₂ hdiff t x ht0 htT
  have hraw :
      |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
        intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤
          (|p.χ₀| * K + L) * T * D :=
    intervalCoupledDuhamelOperator_diff_bound_of_resolver_chemotaxis_bound
      p R u₀ u₁ u₂ hT hL hK hD hL_lip
      (fun s y hs0 hsT => hu₁ s y hs0 hsT)
      (fun s y hs0 hsT => hu₂ s y hs0 hsT)
      (fun s y hs0 hsT => hdiff s y hs0 hsT)
      (fun s y hs0 hsT => hchem u₁ u₂ D hD hu₁ hu₂ hdiff s y hs0 hsT)
      ht0 htT x
      (hint u₁ hu₁ t x ht0 htT)
      (hint u₂ hu₂ t x ht0 htT)
      (hlift_int u₁ hu₁)
      (hlift_int u₂ hu₂)
  have hTD : 0 ≤ T * D := mul_nonneg hT.le hD
  calc
    |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
        intervalCoupledDuhamelOperator p R u₀ u₂ t x|
        ≤ (|p.χ₀| * K + L) * T * D := hraw
    _ = (|p.χ₀| * K + L) * (T * D) := by ring
    _ ≤ A * (T * D) := mul_le_mul_of_nonneg_right hA_bound hTD
    _ = A * T * D := by ring

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

/-- Closed-ball version of the pointwise Picard fixed-point theorem.

This is the form needed for the coupled chemotaxis map: the nonlinear
Lipschitz estimates are local on a trajectory ball, while the Duhamel map is
shown separately to preserve that ball. -/
theorem banach_fixed_point_picard_on_closed_ball
    {Φ : (ℝ → intervalDomainPoint → ℝ) → (ℝ → intervalDomainPoint → ℝ)}
    {M q D₀ : ℝ} (hM : 0 ≤ M) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hD₀ : 0 ≤ D₀)
    (hmap : ∀ u : ℝ → intervalDomainPoint → ℝ,
      (∀ t x, |u t x| ≤ M) → ∀ t x, |Φ u t x| ≤ M)
    (hcontr : ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
      0 ≤ D →
      (∀ t x, |u₁ t x| ≤ M) →
      (∀ t x, |u₂ t x| ≤ M) →
      (∀ s y, |u₁ s y - u₂ s y| ≤ D) →
      ∀ t x, |Φ u₁ t x - Φ u₂ t x| ≤ q * D)
    (hbase : ∀ t x,
      |picardIteration Φ 1 t x - picardIteration Φ 0 t x| ≤ D₀) :
    ∃ u_star : ℝ → intervalDomainPoint → ℝ,
      (∀ t x, |u_star t x| ≤ M) ∧
      ∀ t x, u_star t x = Φ u_star t x := by
  have hpicard_ball :
      ∀ n t x, |picardIteration Φ n t x| ≤ M := by
    intro n
    induction n with
    | zero =>
        intro t x
        simpa [picardIteration] using hM
    | succ n ih =>
        intro t x
        exact hmap (picardIteration Φ n) ih t x
  have hgeom :
      ∀ n t x,
        |picardIteration Φ (n + 1) t x - picardIteration Φ n t x| ≤
          q ^ n * D₀ := by
    intro n
    induction n with
    | zero =>
        intro t x
        simpa using hbase t x
    | succ n ih =>
        intro t x
        change |Φ (picardIteration Φ (n + 1)) t x -
              Φ (picardIteration Φ n) t x| ≤ q ^ (n + 1) * D₀
        have hstep :=
          hcontr (picardIteration Φ (n + 1)) (picardIteration Φ n)
            (q ^ n * D₀) (mul_nonneg (pow_nonneg hq0 n) hD₀)
            (hpicard_ball (n + 1)) (hpicard_ball n) ih t x
        calc |Φ (picardIteration Φ (n + 1)) t x -
              Φ (picardIteration Φ n) t x|
            ≤ q * (q ^ n * D₀) := hstep
          _ = q ^ (n + 1) * D₀ := by ring
  have hcauchy := picard_pointwise_cauchySeq hq0 hq1 hD₀ hgeom
  have hconv : ∀ t x, ∃ L,
      Filter.Tendsto (fun n => picardIteration Φ n t x)
        Filter.atTop (nhds L) :=
    fun t x => ⟨_, (hcauchy t x).tendsto_limUnder⟩
  choose u_star hu_star using fun t => fun x => hconv t x
  have hstar_ball : ∀ t x, |u_star t x| ≤ M := by
    intro t x
    exact le_of_tendsto (hu_star t x).abs
      (Filter.eventually_atTop.mpr ⟨0, fun n _hn => hpicard_ball n t x⟩)
  refine ⟨u_star, hstar_ball, ?_⟩
  intro t x
  have h1q : (0 : ℝ) < 1 - q := sub_pos.mpr hq1
  have htail := picard_tail_bound hq0 hq1 hD₀ hgeom u_star hu_star
  have hfp_bound : ∀ n : ℕ,
      |u_star t x - Φ u_star t x| ≤ 2 * D₀ * q ^ (n + 1) / (1 - q) := by
    intro n
    have hpicard_succ : picardIteration Φ (n + 1) t x =
        Φ (picardIteration Φ n) t x := rfl
    have hdiff_n : ∀ s y,
        |picardIteration Φ n s y - u_star s y| ≤ D₀ * q ^ n / (1 - q) := by
      intro s y
      rw [abs_sub_comm]
      exact htail n s y
    have htail_nonneg : 0 ≤ D₀ * q ^ n / (1 - q) :=
      div_nonneg (mul_nonneg hD₀ (pow_nonneg hq0 n)) h1q.le
    have hPhicontr : |Φ (picardIteration Φ n) t x - Φ u_star t x| ≤
        q * (D₀ * q ^ n / (1 - q)) :=
      hcontr _ _ _ htail_nonneg (hpicard_ball n) hstar_ball hdiff_n t x
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
  have habs_nn : 0 ≤ |u_star t x - Φ u_star t x| := abs_nonneg _
  have hzero : |u_star t x - Φ u_star t x| = 0 := by
    apply eq_zero_of_le_geometric_pow habs_nn
      (by positivity : 0 ≤ 2 * D₀ * q / (1 - q)) hq0 hq1
    intro n
    calc |u_star t x - Φ u_star t x|
        ≤ 2 * D₀ * q ^ (n + 1) / (1 - q) := hfp_bound n
      _ = 2 * D₀ * q / (1 - q) * q ^ n := by rw [pow_succ]; ring
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

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

/-- Local Picard/Banach fixed-point extraction specialized to the concrete
interval Duhamel operator.

This is the local-in-time mild-solution construction step: once the concrete
operator `intervalDuhamelOperator p u₀` is contractive on `[0,T]` with factor
`L * T < 1` and its first Picard step is bounded there by `D₀`, the Picard
construction yields a trajectory fixed point on `[0,T]`.  The proof feeds a
time-truncated operator to the existing Picard/Banach theorem, so no global
in-time contraction is assumed.  No arbitrary-domain regularity API is used
here. -/
theorem intervalDuhamel_fixed_point_exists_of_contraction
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {L D₀ T : ℝ} (hL : 0 < L) (hD₀ : 0 ≤ D₀)
    (hT : 0 < T) (hLT : L * T < 1)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalDuhamelOperator p u₀ u₁ t x -
            intervalDuhamelOperator p u₀ u₂ t x| ≤ L * T * D)
    (hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ D₀) :
    ∃ u : ℝ → intervalDomainPoint → ℝ,
      ∀ t x, 0 ≤ t → t ≤ T →
        u t x = intervalDuhamelOperator p u₀ u t x := by
  let Φ : (ℝ → intervalDomainPoint → ℝ) →
      (ℝ → intervalDomainPoint → ℝ) :=
    fun u t x =>
      if 0 ≤ t ∧ t ≤ T then intervalDuhamelOperator p u₀ u t x else 0
  have hcontr' :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        (∀ s y, |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, |Φ u₁ t x - Φ u₂ t x| ≤ L * T * D := by
    intro u₁ u₂ D hD hdiff t x
    by_cases ht : 0 ≤ t ∧ t ≤ T
    · simpa [Φ, ht] using
        hcontr u₁ u₂ D hD (fun s y _hs0 _hsT => hdiff s y) t x ht.1 ht.2
    · simp [Φ, ht, mul_nonneg (mul_nonneg hL.le hT.le) hD]
  have hbase' :
      ∀ t x, |picardIteration Φ 1 t x - picardIteration Φ 0 t x| ≤ D₀ := by
    intro t x
    by_cases ht : 0 ≤ t ∧ t ≤ T
    · simpa [picardIteration, Φ, ht] using hbase t x ht.1 ht.2
    · simp [picardIteration, Φ, ht, hD₀]
  obtain ⟨u, hfp⟩ :=
    duhamel_mild_solution_exists hL hD₀ hT hLT hcontr' hbase'
  refine ⟨u, ?_⟩
  intro t x ht0 htT
  have ht : 0 ≤ t ∧ t ≤ T := ⟨ht0, htT⟩
  simpa [Φ, ht] using hfp t x

/-- Uniqueness of bounded local fixed points for the concrete interval Duhamel
operator.

This is the uniqueness part supplied by the same contraction estimate as the
Picard construction.  The hypothesis `hbound` is the ball/bounded-distance
input for the two candidate trajectories on `[0,T]`; Picard iteration provides
that bound automatically for fixed points lying in the contraction ball. -/
theorem intervalDuhamel_fixed_point_unique_of_contraction
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {L T D : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (hT : 0 < T) (hLT : L * T < 1)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D' : ℝ),
        0 ≤ D' →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D') →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalDuhamelOperator p u₀ u₁ t x -
            intervalDuhamelOperator p u₀ u₂ t x| ≤ L * T * D')
    {u₁ u₂ : ℝ → intervalDomainPoint → ℝ}
    (hfp₁ :
      ∀ t x, 0 ≤ t → t ≤ T →
        u₁ t x = intervalDuhamelOperator p u₀ u₁ t x)
    (hfp₂ :
      ∀ t x, 0 ≤ t → t ≤ T →
        u₂ t x = intervalDuhamelOperator p u₀ u₂ t x)
    (hbound :
      ∀ t x, 0 ≤ t → t ≤ T → |u₁ t x - u₂ t x| ≤ D) :
    ∀ t x, 0 ≤ t → t ≤ T → u₁ t x = u₂ t x := by
  let q : ℝ := L * T
  have hq0 : 0 ≤ q := by
    exact mul_nonneg hL.le hT.le
  have hpow_bound :
      ∀ n t x, 0 ≤ t → t ≤ T →
        |u₁ t x - u₂ t x| ≤ q ^ n * D := by
    intro n
    induction n with
    | zero =>
        intro t x ht0 htT
        simpa using hbound t x ht0 htT
    | succ n ih =>
        intro t x ht0 htT
        rw [hfp₁ t x ht0 htT, hfp₂ t x ht0 htT]
        calc
          |intervalDuhamelOperator p u₀ u₁ t x -
              intervalDuhamelOperator p u₀ u₂ t x|
              ≤ L * T * (q ^ n * D) :=
                hcontr u₁ u₂ (q ^ n * D)
                  (mul_nonneg (pow_nonneg hq0 n) hD)
                  (fun s y hs0 hsT => ih s y hs0 hsT) t x ht0 htT
          _ = q ^ (n + 1) * D := by
                simp [q, pow_succ]
                ring
  intro t x ht0 htT
  have habs_zero : |u₁ t x - u₂ t x| = 0 := by
    apply eq_zero_of_le_geometric_pow (abs_nonneg _) hD hq0 hLT
    intro n
    calc
      |u₁ t x - u₂ t x| ≤ q ^ n * D := hpow_bound n t x ht0 htT
      _ = D * q ^ n := by ring
  exact sub_eq_zero.mp (abs_eq_zero.mp habs_zero)

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
    (∀ t x, 0 < t → t < T → 0 < u t x) ∧
    -- Nonnegativity of the chemical concentration `v` (positive classical sol.)
    (∀ t x, 0 < t → t < T → 0 ≤ v t x) ∧
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
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨v, hfp, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩

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

/-- Concrete interval-Duhamel Banach fixed point plus concrete Duhamel
regularization gives local classical existence.

The only regularity input is `hregularize`: it must upgrade the fixed point of
the concrete Picard/Duhamel operator to `RegularityBootstrap`.  This avoids the
invalid arbitrary-domain regularity shortcut exposed by the `not_forall`
counterexamples. -/
theorem localExistence_of_intervalDuhamel_contraction_and_regularization
    (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {L D₀ T : ℝ} (hL : 0 < L) (hD₀ : 0 ≤ D₀)
    (hT : 0 < T) (hLT : L * T < 1)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalDuhamelOperator p u₀ u₁ t x -
            intervalDuhamelOperator p u₀ u₂ t x| ≤ L * T * D)
    (hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ D₀)
    (hregularize :
      ∀ u : ℝ → intervalDomainPoint → ℝ,
        (∀ t x, 0 ≤ t → t ≤ T →
          u t x = intervalDuhamelOperator p u₀ u t x) →
          RegularityBootstrap p T u₀ u) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  obtain ⟨u, hfp⟩ :=
    intervalDuhamel_fixed_point_exists_of_contraction p u₀
      hL hD₀ hT hLT hcontr hbase
  exact localExistence_of_fp_and_regularity p u₀ hu₀ hT hfp
    (hregularize u hfp)

/-- Uniform local-existence closure from the concrete interval-Duhamel Picard
iteration.

For every positive initial datum, if the concrete Duhamel map has a local
contraction estimate on `[0,T]`, the first Picard step is bounded there, and
the resulting fixed point is regularized by the concrete Duhamel iteration into
`RegularityBootstrap`, then every positive initial datum launches a local
classical solution with initial trace.

This is the local-existence part of Paper 2 Proposition 1.1.  It deliberately
does not assert the finite-horizon blow-up/vanishing alternative, which is a
separate maximal-continuation theorem rather than a consequence of the
short-time Picard construction. -/
theorem intervalDomain_localExistence_of_intervalDuhamel_contraction_regularization
    (p : CM2Params)
    (hmild :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ L > 0, ∃ D₀ ≥ 0, ∃ T > 0,
            L * T < 1 ∧
            (∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
              0 ≤ D →
              (∀ s y, 0 ≤ s → s ≤ T →
                |u₁ s y - u₂ s y| ≤ D) →
              ∀ t x, 0 ≤ t → t ≤ T →
                |intervalDuhamelOperator p u₀ u₁ t x -
                  intervalDuhamelOperator p u₀ u₂ t x| ≤ L * T * D) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ D₀) ∧
            (∀ u : ℝ → intervalDomainPoint → ℝ,
              (∀ t x, 0 ≤ t → t ≤ T →
                u t x = intervalDuhamelOperator p u₀ u t x) →
                RegularityBootstrap p T u₀ u)) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨L, hL, D₀, hD₀, T, hT, hLT, hcontr, hbase, hregularize⟩ :=
    hmild u₀ hu₀
  exact localExistence_of_intervalDuhamel_contraction_and_regularization
    p u₀ hu₀ hL hD₀ hT hLT hcontr hbase hregularize

/-- Full `Proposition_1_1 intervalDomain p` from a closed local-existence
theorem plus the genuine finite-horizon alternative.

The first hypothesis is exactly the local branch closed by
`intervalDomain_localExistence_of_intervalDuhamel_contraction_regularization`.
The second hypothesis is the remaining maximal-time/blow-up alternative. -/
theorem Proposition_1_1_intervalDomain_of_localExistence_and_finiteHorizonAlternative
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (halternative :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          FiniteHorizonAlternative intervalDomain Tmax u ∧
          (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)) :
    Proposition_1_1 intervalDomain p := by
  intro u₀ hu₀
  obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ := hlocal u₀ hu₀.toPositive
  obtain ⟨halt, hmge⟩ :=
    halternative u₀ hu₀.toPositive Tmax hTmax u v hsol htrace
  exact ⟨Tmax, hTmax, u, v, hsol, htrace, halt, hmge⟩

/-- Conditional `Proposition_1_1` assembly from the concrete interval-Duhamel
Banach construction.

The short-time fixed point and classical local solution are produced by
`intervalDuhamel_fixed_point_exists_of_contraction` plus the concrete
Duhamel-regularization frontier.  The remaining hypothesis `hmaximal` is the
honest maximal-continuation/blow-up alternative frontier: it is not a
consequence of a local Banach fixed point on a fixed short time interval. -/
theorem Proposition_1_1_intervalDomain_of_intervalDuhamel_contraction_regularization
    (p : CM2Params)
    (hmild :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ L > 0, ∃ D₀ ≥ 0, ∃ T > 0,
            L * T < 1 ∧
            (∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
              0 ≤ D →
              (∀ s y, 0 ≤ s → s ≤ T →
                |u₁ s y - u₂ s y| ≤ D) →
              ∀ t x, 0 ≤ t → t ≤ T →
                |intervalDuhamelOperator p u₀ u₁ t x -
                  intervalDuhamelOperator p u₀ u₂ t x| ≤ L * T * D) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ D₀) ∧
            (∀ u : ℝ → intervalDomainPoint → ℝ,
              (∀ t x, 0 ≤ t → t ≤ T →
                u t x = intervalDuhamelOperator p u₀ u t x) →
                RegularityBootstrap p T u₀ u))
    (hmaximal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          FiniteHorizonAlternative intervalDomain Tmax u ∧
          (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)) :
    Proposition_1_1 intervalDomain p := by
  intro u₀ hu₀
  obtain ⟨L, hL, D₀, hD₀, T, hT, hLT, hcontr, hbase, hregularize⟩ :=
    hmild u₀ hu₀.toPositive
  obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ :=
    localExistence_of_intervalDuhamel_contraction_and_regularization p u₀ hu₀.toPositive
      hL hD₀ hT hLT hcontr hbase hregularize
  obtain ⟨halt, hmge⟩ := hmaximal u₀ hu₀.toPositive Tmax hTmax u v hsol htrace
  exact ⟨Tmax, hTmax, u, v, hsol, htrace, halt, hmge⟩

/-! ### Maximal-continuation order skeleton

The standard continuation proof starts from the set of horizons on which a
classical solution exists with the prescribed initial trace.  If these horizons
are unbounded, the continuation is global.  If they are bounded, the finite
maximal time is the supremum of that set.  The analytic continuation step still
has to prove that bounded, positive finite-time behavior lets one extend past
the supremum; the lemmas below are the order-theoretic part of that argument. -/

/-- A time horizon is reachable if there is a classical interval solution up to
that horizon with the prescribed initial trace. -/
def ReachableClassicalHorizon
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  0 < T ∧
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v ∧
      InitialTrace intervalDomain u₀ u

/-- The set of all reachable classical horizons for the initial datum. -/
def reachableClassicalHorizonSet
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Set ℝ :=
  {T | ReachableClassicalHorizon p u₀ T}

/-- The global branch of the standard maximal-continuation statement:
arbitrarily long finite horizons are reachable. -/
def ReachableArbitrarilyLong
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ∀ T > 0, ReachableClassicalHorizon p u₀ T

/-- The finite branch of the standard maximal-continuation statement, matching
the current formal `Proposition_1_1` finite-horizon fields. -/
def FiniteContinuationAlternativeBranch
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
    InitialTrace intervalDomain u₀ u ∧
    FiniteHorizonAlternative intervalDomain Tmax u ∧
    (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)

/-- Standard maximal-continuation conclusion for one initial datum: either all
finite horizons are reachable, or a finite maximal-time alternative occurs. -/
def StandardContinuationAlternative
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ReachableArbitrarilyLong p u₀ ∨
    FiniteContinuationAlternativeBranch p u₀

/-- Local existence makes the reachable-horizon set nonempty. -/
theorem reachableClassicalHorizonSet_nonempty_of_localExistence
    (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (hlocal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2ClassicalSolution intervalDomain p T u v ∧
            InitialTrace intervalDomain u₀ u)
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    (reachableClassicalHorizonSet p u₀).Nonempty := by
  obtain ⟨T, hT, u, v, hsol, htrace⟩ := hlocal u₀ hu₀
  exact ⟨T, hT, u, v, hsol, htrace⟩

/-- Finite candidate for the maximal reachable horizon, used only in the
bounded-horizon branch.  In the global branch the reachable horizons are
unbounded, so no finite `sSup` represents the maximal time. -/
noncomputable def finiteMaximalReachableHorizon
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℝ :=
  sSup (reachableClassicalHorizonSet p u₀)

/-- Any reachable horizon lies below the finite supremum, provided the
reachable-horizon set is bounded above. -/
theorem reachable_le_finiteMaximalReachableHorizon
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hT : ReachableClassicalHorizon p u₀ T) :
    T ≤ finiteMaximalReachableHorizon p u₀ := by
  exact le_csSup hbdd hT

/-- If local existence gives a positive reachable horizon and the reachable
set is bounded above, then the finite supremum is positive. -/
theorem finiteMaximalReachableHorizon_pos_of_localExistence
    (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (hlocal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2ClassicalSolution intervalDomain p T u v ∧
            InitialTrace intervalDomain u₀ u)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀)) :
    0 < finiteMaximalReachableHorizon p u₀ := by
  obtain ⟨T, hTmem⟩ :=
    reachableClassicalHorizonSet_nonempty_of_localExistence p hlocal hu₀
  exact lt_of_lt_of_le hTmem.1
    (reachable_le_finiteMaximalReachableHorizon hbdd hTmem)

/-- A horizon can be continued past if a strictly larger classical horizon is
reachable with the same initial trace. -/
def ReachablePast
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∃ T' > T, ReachableClassicalHorizon p u₀ T'

/-- The finite `sSup` of the reachable horizons is order-maximal: no strictly
larger reachable horizon exists.  The analytic continuation theorem has to
contradict this by constructing such a larger horizon from bounded positive
finite-time behavior. -/
theorem not_reachablePast_finiteMaximalReachableHorizon
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀)) :
    ¬ ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀) := by
  intro h
  rcases h with ⟨T', hgt, hT'⟩
  exact not_lt_of_ge
    (reachable_le_finiteMaximalReachableHorizon hbdd hT') hgt

/-- Sup-norm monotonicity regularity restricts to smaller time sets. -/
lemma intervalDomainSupNormDerivativeNonposOn_mono
    {u : ℝ → intervalDomainPoint → ℝ} {I J : Set ℝ}
    (h : IntervalDomainSupNormDerivativeNonposOn u I) (hJI : J ⊆ I) :
    IntervalDomainSupNormDerivativeNonposOn u J := by
  refine ⟨h.continuousOn.mono hJI, ?_, ?_⟩
  · exact h.differentiableOn.mono (interior_mono hJI)
  · intro t ht
    exact h.deriv_nonpos t ((interior_mono hJI) ht)

/-- `intervalDomainClassicalRegularity` restricts from a longer horizon to a
shorter horizon. -/
lemma intervalDomainClassicalRegularity_mono
    {Tshort Tlong : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hTL : Tshort ≤ Tlong)
    (hreg : intervalDomainClassicalRegularity Tlong u v) :
    intervalDomainClassicalRegularity Tshort u v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hreg.1 t ⟨ht.1, lt_of_lt_of_le ht.2 hTL⟩
  · intro x t ht
    obtain ⟨hdiff, hcontU, hcontV⟩ :=
      hreg.2.1 x t ⟨ht.1, lt_of_lt_of_le ht.2 hTL⟩
    exact ⟨hdiff,
      hcontU.mono (Set.Ioo_subset_Ioo_right hTL),
      hcontV.mono (Set.Ioo_subset_Ioo_right hTL)⟩
  · obtain ⟨hjU, hjV⟩ := hreg.2.2.1
    exact ⟨hjU.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right hTL) (le_refl _)),
      hjV.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right hTL) (le_refl _))⟩
  · intro t ht
    exact hreg.2.2.2.1 t ⟨ht.1, lt_of_lt_of_le ht.2 hTL⟩
  · intro t ht
    exact hreg.2.2.2.2.1 t ⟨ht.1, lt_of_lt_of_le ht.2 hTL⟩
  · obtain ⟨hjU, hjV⟩ := hreg.2.2.2.2.2.1
    exact ⟨hjU.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right hTL) (le_refl _)),
      hjV.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right hTL) (le_refl _))⟩
  · obtain ⟨hjU, hjV⟩ := hreg.2.2.2.2.2.2
    exact ⟨hjU.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right hTL) (le_refl _)),
      hjV.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right hTL) (le_refl _))⟩

/-- A classical interval solution on a longer horizon is also a classical
solution on every positive shorter horizon. -/
theorem isPaper2ClassicalSolution_intervalDomain_mono
    {p : CM2Params} {Tshort Tlong : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hsol : IsPaper2ClassicalSolution intervalDomain p Tlong u v) :
    IsPaper2ClassicalSolution intervalDomain p Tshort u v :=
  IsPaper2ClassicalSolution.of_components hTshort
    (intervalDomainClassicalRegularity_mono (u := u) (v := v)
      hTL hsol.regularity)
    (fun _t _x ht0 htT =>
      hsol.u_pos' ht0 (lt_of_lt_of_le htT hTL))
    (fun _t _x ht0 htT =>
      hsol.v_nonneg ht0 (lt_of_lt_of_le htT hTL))
    (fun _t _x ht0 htT hx =>
      hsol.pde_u ht0 (lt_of_lt_of_le htT hTL) hx)
    (fun _t _x ht0 htT hx =>
      hsol.pde_v ht0 (lt_of_lt_of_le htT hTL) hx)
    (fun _t _x ht0 htT hx =>
      hsol.neumann ht0 (lt_of_lt_of_le htT hTL) hx)

/-- Reachability is downward closed in the time horizon. -/
theorem reachableClassicalHorizon_mono
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {Tshort Tlong : ℝ}
    (hTshort : 0 < Tshort) (hTL : Tshort ≤ Tlong)
    (hreach : ReachableClassicalHorizon p u₀ Tlong) :
    ReachableClassicalHorizon p u₀ Tshort := by
  rcases hreach with ⟨_hTlong, u, v, hsol, htrace⟩
  exact ⟨hTshort, u, v,
    isPaper2ClassicalSolution_intervalDomain_mono hTshort hTL hsol, htrace⟩

/-- If reachable horizons are not bounded above, then every finite positive
horizon is reachable. -/
theorem reachableArbitrarilyLong_of_not_bddAbove
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hnbdd : ¬ BddAbove (reachableClassicalHorizonSet p u₀)) :
    ReachableArbitrarilyLong p u₀ := by
  intro T hT
  obtain ⟨Tlong, hTlong, hlt⟩ := (not_bddAbove_iff.mp hnbdd) T
  exact reachableClassicalHorizon_mono hT (le_of_lt hlt) hTlong

/-- Standard maximal-continuation theorem, with the two genuine analytic
frontiers left explicit.

The proof is now purely order-theoretic:
* if the reachable-horizon set is unbounded, downward closure gives the global
  branch;
* if it is bounded, local existence makes the finite `sSup` positive;
* a realized classical solution at that `sSup` must satisfy both finite-time
  alternatives, because failure of either alternative is assumed to construct a
  larger reachable horizon, contradicting `sSup` maximality.

The hypotheses `hrealize`, `hextend_of_not_finiteAlternative`, and
`hextend_of_not_mgeAlternative` are precisely the missing PDE continuation
content: compactness/gluing at the finite supremum, endpoint traces, restart
local existence, and uniqueness needed to paste the old and restarted
solutions. -/
theorem standardContinuationAlternative_of_finiteSup_realization_and_extension
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hlocal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2ClassicalSolution intervalDomain p T u v ∧
            InitialTrace intervalDomain u₀ u)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hrealize :
      ∀ _hbdd : BddAbove (reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomainPoint → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomainPoint → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀)) :
    StandardContinuationAlternative p u₀ := by
  by_cases hbdd : BddAbove (reachableClassicalHorizonSet p u₀)
  · right
    have hTmax_pos :
        0 < finiteMaximalReachableHorizon p u₀ :=
      finiteMaximalReachableHorizon_pos_of_localExistence p hlocal hu₀ hbdd
    obtain ⟨u, v, hsol, htrace⟩ := hrealize hbdd
    refine ⟨finiteMaximalReachableHorizon p u₀, hTmax_pos, u, v,
      hsol, htrace, ?_, ?_⟩
    · by_contra hnot
      exact not_reachablePast_finiteMaximalReachableHorizon hbdd
        (hextend_of_not_finiteAlternative hbdd hsol htrace hnot)
    · intro hm
      by_contra hnot
      exact not_reachablePast_finiteMaximalReachableHorizon hbdd
        (hextend_of_not_mgeAlternative hbdd hsol htrace hm hnot)
  · left
    exact reachableArbitrarilyLong_of_not_bddAbove hbdd

/-- The already constructed positive equilibrium lies in the global branch of
the standard continuation alternative: every finite horizon is reachable. -/
theorem equilibrium_reachableArbitrarilyLong
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    ReachableArbitrarilyLong p
      (constOnInterval ((p.a / p.b) ^ (1 / p.α))) := by
  intro T hT
  refine ⟨hT, ?_⟩
  exact ⟨fun _ _ => (p.a / p.b) ^ (1 / p.α),
    fun _ _ => ellipticV p ((p.a / p.b) ^ (1 / p.α)),
    (equilibrium_isPaper2ClassicalSolution p ha hb) T hT,
    constantSolution_initialTrace ((p.a / p.b) ^ (1 / p.α))⟩

/-- For positive equilibrium data, the reachable-horizon set is genuinely
unbounded.  This is the formal obstruction to replacing the global branch of
maximal continuation by a finite `Tmax` alternative. -/
theorem equilibrium_reachableClassicalHorizonSet_not_bddAbove
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    ¬ BddAbove (reachableClassicalHorizonSet p
      (constOnInterval ((p.a / p.b) ^ (1 / p.α)))) := by
  rw [not_bddAbove_iff]
  intro T
  let Tlong : ℝ := max (T + 1) 1
  have hTlong_pos : 0 < Tlong :=
    lt_of_lt_of_le zero_lt_one (le_max_right (T + 1) (1 : ℝ))
  have hT_lt_Tlong : T < Tlong :=
    lt_of_lt_of_le (lt_add_one T) (le_max_left (T + 1) (1 : ℝ))
  exact ⟨Tlong,
    equilibrium_reachableArbitrarilyLong p ha hb Tlong hTlong_pos,
    hT_lt_Tlong⟩

/-- Consequently the standard maximal-continuation statement for equilibrium
data closes by the global branch, not by the finite alternative branch used in
the current formal `Proposition_1_1`. -/
theorem equilibrium_standardContinuationAlternative_global
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    StandardContinuationAlternative p
      (constOnInterval ((p.a / p.b) ^ (1 / p.α))) :=
  Or.inl (equilibrium_reachableArbitrarilyLong p ha hb)

/-- Scalar ODE uniqueness at the positive logistic equilibrium.  This is the
ODE-side uniqueness component used by continuation/gluing arguments for
spatially constant restart data. -/
theorem equilibrium_logisticProfile_unique
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b)
    {T m M : ℝ} (hm : 0 < m)
    (hc_mem :
      (p.a / p.b) ^ (1 / p.α) ∈ Set.Icc m M)
    {φ : ℝ → ℝ}
    (hφ_cont : ContinuousOn φ (Set.Icc 0 T))
    (hφ_ode : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt φ (bernoulliLogisticVectorField p (φ t)) t)
    (hφ_mem : ∀ t ∈ Set.Ico (0 : ℝ) T, φ t ∈ Set.Icc m M)
    (hinit : φ 0 = (p.a / p.b) ^ (1 / p.α)) :
    Set.EqOn φ (fun _ : ℝ => (p.a / p.b) ^ (1 / p.α))
      (Set.Icc 0 T) := by
  let c : ℝ := (p.a / p.b) ^ (1 / p.α)
  have hconst_cont : ContinuousOn (fun _ : ℝ => c) (Set.Icc 0 T) :=
    continuous_const.continuousOn
  have hfield_c : bernoulliLogisticVectorField p c = 0 := by
    rw [bernoulliLogisticVectorField]
    dsimp [c]
    rw [equilibrium_reaction_zero p ha hb]
    ring
  have hconst_ode : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt (fun _ : ℝ => c)
        (bernoulliLogisticVectorField p ((fun _ : ℝ => c) t)) t := by
    intro t ht
    simpa [hfield_c] using hasDerivAt_const t c
  have hconst_mem : ∀ t ∈ Set.Ico (0 : ℝ) T,
      (fun _ : ℝ => c) t ∈ Set.Icc m M := by
    intro t ht
    exact hc_mem
  simpa [c] using
    bernoulliLogistic_unique p hm hφ_cont hφ_ode hφ_mem
      hconst_cont hconst_ode hconst_mem hinit

/-! ### Finite-horizon alternative diagnostics

The formal `FiniteHorizonAlternative` in `Paper2.Statements` is a genuine
maximal-time conclusion: at the chosen finite `Tmax`, the solution must either
be pointwise unbounded from above or approach zero somewhere in the interior.
The following lemmas record a hard obstruction for the local-existence branch:
a positive spatially constant local witness satisfies neither alternative.
Thus this field cannot be manufactured from the short-time Picard solution; it
needs an independent maximal-continuation theorem, or the statement must be
changed to quantify over the actual maximal time. -/

/-- A positive spatially constant trajectory is neither unbounded nor
vanishing, so it cannot satisfy the stated finite-horizon alternative. -/
theorem const_positive_not_finiteHorizonAlternative
    {T c : ℝ} (hc : 0 < c) :
    ¬ FiniteHorizonAlternative intervalDomain T
        (fun _ (_ : intervalDomainPoint) => c) := by
  intro h
  rcases h with hunbounded | hvanishes
  · rcases hunbounded c with ⟨t, x, ht0, htT, hx, hlt⟩
    simp at hlt
  · rcases hvanishes (c / 2) (half_pos hc) with
      ⟨t, x, ht0, htT, hx, hlt⟩
    linarith

/-- A spatially constant trajectory cannot satisfy the `m ≥ 1` blow-up-only
alternative. -/
theorem const_not_mgeOneFiniteHorizonAlternative
    {T c : ℝ} :
    ¬ MGeOneFiniteHorizonAlternative intervalDomain T
        (fun _ (_ : intervalDomainPoint) => c) := by
  intro h
  rcases h c with ⟨t, x, ht0, htT, hx, hlt⟩
  simp at hlt

/-- The positive equilibrium witness already proved in this file cannot be
used to close the formal finite-horizon alternative field. -/
theorem equilibrium_witness_not_finiteHorizonAlternative
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) {T : ℝ} :
    ¬ FiniteHorizonAlternative intervalDomain T
        (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α)) :=
  const_positive_not_finiteHorizonAlternative (equilibrium_pos p ha hb)

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
  refine ⟨fun _ _ => ellipticV p c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Positivity
    exact fun _t _x _ht0 _htT => hc
  · -- v-nonnegativity
    exact fun _t _x _ht0 _htT => (ellipticV_pos p hc).le
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
  refine ⟨fun _ _ => ellipticV p c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Positivity
    exact fun _t _x _ht0 _htT => hc
  · -- v-nonnegativity
    exact fun _t _x _ht0 _htT => (ellipticV_pos p hc).le
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
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨T, hT, u, v,
    IsPaper2ClassicalSolution.of_components hT hclassreg hpos hvnn hpde_u hpde_v hbc,
    htrace⟩

/-! ### Coupled Duhamel fixed point to local existence

The full chemotaxis-elliptic mild operator was defined before the Picard
machinery.  The extraction theorem is placed here because it depends on both
the Picard/Banach construction and the `RegularityBootstrap` bridge. -/

/-- Concrete Banach extraction for the full coupled parabolic-elliptic mild
operator, with an explicit elliptic resolver `R`.

This is the coupled replacement for the logistic-only
`intervalDuhamel_fixed_point_exists_of_contraction`. -/
theorem intervalCoupledDuhamel_fixed_point_exists_of_contraction
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {L D₀ T : ℝ} (hL : 0 < L) (hD₀ : 0 ≤ D₀)
    (hT : 0 < T) (hLT : L * T < 1)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ L * T * D)
    (hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalCoupledDuhamelOperator p R u₀ (fun _ _ => 0) t x| ≤ D₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      (∀ t x, 0 ≤ t → t ≤ T →
        u t x = intervalCoupledDuhamelOperator p R u₀ u t x) ∧
      (∀ t, v t = R (u t)) := by
  let Φ : (ℝ → intervalDomainPoint → ℝ) →
      (ℝ → intervalDomainPoint → ℝ) :=
    fun u t x =>
      if 0 ≤ t ∧ t ≤ T then intervalCoupledDuhamelOperator p R u₀ u t x else 0
  have hcontr' :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        (∀ s y, |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, |Φ u₁ t x - Φ u₂ t x| ≤ L * T * D := by
    intro u₁ u₂ D hD hdiff t x
    by_cases ht : 0 ≤ t ∧ t ≤ T
    · simpa [Φ, ht] using
        hcontr u₁ u₂ D hD (fun s y _hs0 _hsT => hdiff s y) t x ht.1 ht.2
    · simp [Φ, ht, mul_nonneg (mul_nonneg hL.le hT.le) hD]
  have hbase' :
      ∀ t x, |picardIteration Φ 1 t x - picardIteration Φ 0 t x| ≤ D₀ := by
    intro t x
    by_cases ht : 0 ≤ t ∧ t ≤ T
    · simpa [picardIteration, Φ, ht] using hbase t x ht.1 ht.2
    · simp [picardIteration, Φ, ht, hD₀]
  obtain ⟨u, hfp⟩ :=
    duhamel_mild_solution_exists hL hD₀ hT hLT hcontr' hbase'
  refine ⟨u, fun t => R (u t), ?_, fun _ => rfl⟩
  intro t x ht0 htT
  have ht : 0 ≤ t ∧ t ≤ T := ⟨ht0, htT⟩
  simpa [Φ, ht] using hfp t x

/-- Closed-ball Banach extraction for the coupled Duhamel map.

Unlike `intervalCoupledDuhamel_fixed_point_exists_of_contraction`, the
contraction hypothesis here is only required on the trajectory ball preserved
by the map.  This is the natural local-existence shape for locally Lipschitz
chemotaxis nonlinearities. -/
theorem intervalCoupledDuhamel_fixed_point_exists_on_closed_ball
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {L D₀ T M : ℝ} (hL : 0 < L) (hD₀ : 0 ≤ D₀)
    (hT : 0 < T) (hLT : L * T < 1) (hM : 0 ≤ M)
    (hmap :
      ∀ u : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
          ∀ t x, 0 ≤ t → t ≤ T →
            |intervalCoupledDuhamelOperator p R u₀ u t x| ≤ M)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        intervalTrajectoryBoundedOn T M u₁ →
        intervalTrajectoryBoundedOn T M u₂ →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ L * T * D)
    (hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalCoupledDuhamelOperator p R u₀ (fun _ _ => 0) t x| ≤ D₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      intervalTrajectoryBoundedOn T M u ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        u t x = intervalCoupledDuhamelOperator p R u₀ u t x) ∧
      (∀ t, v t = R (u t)) := by
  let Φ : (ℝ → intervalDomainPoint → ℝ) →
      (ℝ → intervalDomainPoint → ℝ) :=
    fun u t x =>
      if 0 ≤ t ∧ t ≤ T then intervalCoupledDuhamelOperator p R u₀ u t x else 0
  have hmap' :
      ∀ u : ℝ → intervalDomainPoint → ℝ,
        (∀ t x, |u t x| ≤ M) → ∀ t x, |Φ u t x| ≤ M := by
    intro u hu t x
    by_cases ht : 0 ≤ t ∧ t ≤ T
    · simpa [Φ, ht] using
        hmap u (fun s y hs0 hsT => hu s y) t x ht.1 ht.2
    · simp [Φ, ht, hM]
  have hcontr' :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        (∀ t x, |u₁ t x| ≤ M) →
        (∀ t x, |u₂ t x| ≤ M) →
        (∀ s y, |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, |Φ u₁ t x - Φ u₂ t x| ≤ L * T * D := by
    intro u₁ u₂ D hD hu₁ hu₂ hdiff t x
    by_cases ht : 0 ≤ t ∧ t ≤ T
    · simpa [Φ, ht] using
        hcontr u₁ u₂ D hD
          (fun s y _hs0 _hsT => hu₁ s y)
          (fun s y _hs0 _hsT => hu₂ s y)
          (fun s y _hs0 _hsT => hdiff s y)
          t x ht.1 ht.2
    · simp [Φ, ht, mul_nonneg (mul_nonneg hL.le hT.le) hD]
  have hbase' :
      ∀ t x, |picardIteration Φ 1 t x - picardIteration Φ 0 t x| ≤ D₀ := by
    intro t x
    by_cases ht : 0 ≤ t ∧ t ≤ T
    · simpa [picardIteration, Φ, ht] using hbase t x ht.1 ht.2
    · simp [picardIteration, Φ, ht, hD₀]
  obtain ⟨u, hu_ball, hfp⟩ :=
    banach_fixed_point_picard_on_closed_ball hM
      (mul_nonneg hL.le hT.le) hLT hD₀ hmap' hcontr' hbase'
  refine ⟨u, fun t => R (u t), ?_, ?_, fun _ => rfl⟩
  · intro t x _ht0 _htT
    exact hu_ball t x
  · intro t x ht0 htT
    have ht : 0 ≤ t ∧ t ≤ T := ⟨ht0, htT⟩
    simpa [Φ, ht] using hfp t x

/-- Uniqueness of bounded local fixed points for the full coupled Duhamel
operator after substituting the elliptic resolver. -/
theorem intervalCoupledDuhamel_fixed_point_unique_of_contraction
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {L T D : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (hT : 0 < T) (hLT : L * T < 1)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D' : ℝ),
        0 ≤ D' →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D') →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ L * T * D')
    {u₁ u₂ : ℝ → intervalDomainPoint → ℝ}
    (hfp₁ :
      ∀ t x, 0 ≤ t → t ≤ T →
        u₁ t x = intervalCoupledDuhamelOperator p R u₀ u₁ t x)
    (hfp₂ :
      ∀ t x, 0 ≤ t → t ≤ T →
        u₂ t x = intervalCoupledDuhamelOperator p R u₀ u₂ t x)
    (hbound :
      ∀ t x, 0 ≤ t → t ≤ T → |u₁ t x - u₂ t x| ≤ D) :
    ∀ t x, 0 ≤ t → t ≤ T → u₁ t x = u₂ t x := by
  let q : ℝ := L * T
  have hq0 : 0 ≤ q := by
    exact mul_nonneg hL.le hT.le
  have hpow_bound :
      ∀ n t x, 0 ≤ t → t ≤ T →
        |u₁ t x - u₂ t x| ≤ q ^ n * D := by
    intro n
    induction n with
    | zero =>
        intro t x ht0 htT
        simpa using hbound t x ht0 htT
    | succ n ih =>
        intro t x ht0 htT
        rw [hfp₁ t x ht0 htT, hfp₂ t x ht0 htT]
        calc
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
              intervalCoupledDuhamelOperator p R u₀ u₂ t x|
              ≤ L * T * (q ^ n * D) :=
                hcontr u₁ u₂ (q ^ n * D)
                  (mul_nonneg (pow_nonneg hq0 n) hD)
                  (fun s y hs0 hsT => ih s y hs0 hsT) t x ht0 htT
          _ = q ^ (n + 1) * D := by
                simp [q, pow_succ]
                ring
  intro t x ht0 htT
  have habs_zero : |u₁ t x - u₂ t x| = 0 := by
    apply eq_zero_of_le_geometric_pow (abs_nonneg _) hD hq0 hLT
    intro n
    calc
      |u₁ t x - u₂ t x| ≤ q ^ n * D := hpow_bound n t x ht0 htT
      _ = D * q ^ n := by ring
  exact sub_eq_zero.mp (abs_eq_zero.mp habs_zero)

/-- Product-form uniqueness for coupled mild fixed points, including the
elliptic component `v = R u`. -/
theorem intervalCoupledDuhamel_solution_unique_of_contraction
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    {L T D : ℝ} (hL : 0 < L) (hD : 0 ≤ D)
    (hT : 0 < T) (hLT : L * T < 1)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D' : ℝ),
        0 ≤ D' →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D') →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ L * T * D')
    {u₁ u₂ v₁ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hfp₁ :
      ∀ t x, 0 ≤ t → t ≤ T →
        u₁ t x = intervalCoupledDuhamelOperator p R u₀ u₁ t x)
    (hfp₂ :
      ∀ t x, 0 ≤ t → t ≤ T →
        u₂ t x = intervalCoupledDuhamelOperator p R u₀ u₂ t x)
    (hv₁ : ∀ t, v₁ t = R (u₁ t))
    (hv₂ : ∀ t, v₂ t = R (u₂ t))
    (hbound :
      ∀ t x, 0 ≤ t → t ≤ T → |u₁ t x - u₂ t x| ≤ D) :
    ∀ t x, 0 ≤ t → t ≤ T →
      u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x := by
  have hu_eq :
      ∀ t x, 0 ≤ t → t ≤ T → u₁ t x = u₂ t x :=
    intervalCoupledDuhamel_fixed_point_unique_of_contraction
      p R u₀ hL hD hT hLT hcontr hfp₁ hfp₂ hbound
  intro t x ht0 htT
  refine ⟨hu_eq t x ht0 htT, ?_⟩
  have hfun : u₁ t = u₂ t := by
    funext y
    exact hu_eq t y ht0 htT
  rw [hv₁ t, hv₂ t, hfun]

/-- Coupled Duhamel fixed point plus a concrete regularization theorem yields
local classical existence for the full formal chemotaxis-elliptic system. -/
theorem localExistence_of_coupledDuhamel_contraction_and_regularization
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {L D₀ T : ℝ} (hL : 0 < L) (hD₀ : 0 ≤ D₀)
    (hT : 0 < T) (hLT : L * T < 1)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ L * T * D)
    (hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalCoupledDuhamelOperator p R u₀ (fun _ _ => 0) t x| ≤ D₀)
    (hregularize :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        (∀ t x, 0 ≤ t → t ≤ T →
          u t x = intervalCoupledDuhamelOperator p R u₀ u t x) →
        (∀ t, v t = R (u t)) →
          RegularityBootstrap p T u₀ u) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  obtain ⟨u, v, hfp, hv⟩ :=
    intervalCoupledDuhamel_fixed_point_exists_of_contraction p R u₀
      hL hD₀ hT hLT hcontr hbase
  exact localExistence_of_regularityBootstrap p u₀ hu₀ hT
    (hregularize u v hfp hv)

/-- Closed-ball coupled Duhamel fixed point plus concrete regularization gives
local classical existence. -/
theorem localExistence_of_coupledDuhamel_closedBall_contraction_and_regularization
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {L D₀ T M : ℝ} (hL : 0 < L) (hD₀ : 0 ≤ D₀)
    (hT : 0 < T) (hLT : L * T < 1) (hM : 0 ≤ M)
    (hmap :
      ∀ u : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
          ∀ t x, 0 ≤ t → t ≤ T →
            |intervalCoupledDuhamelOperator p R u₀ u t x| ≤ M)
    (hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        intervalTrajectoryBoundedOn T M u₁ →
        intervalTrajectoryBoundedOn T M u₂ →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ L * T * D)
    (hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalCoupledDuhamelOperator p R u₀ (fun _ _ => 0) t x| ≤ D₀)
    (hregularize :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
        (∀ t x, 0 ≤ t → t ≤ T →
          u t x = intervalCoupledDuhamelOperator p R u₀ u t x) →
        (∀ t, v t = R (u t)) →
          RegularityBootstrap p T u₀ u) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  obtain ⟨u, v, hu_ball, hfp, hv⟩ :=
    intervalCoupledDuhamel_fixed_point_exists_on_closed_ball p R u₀
      hL hD₀ hT hLT hM hmap hcontr hbase
  exact localExistence_of_regularityBootstrap p u₀ hu₀ hT
    (hregularize u v hu_ball hfp hv)

/-- Local classical existence from the resolver ball estimates plus a concrete
regularization theorem.

Once the Neumann elliptic resolver file supplies
`IntervalCoupledResolverBallEstimates`, this theorem is the import point that
turns those estimates into the coupled mild fixed point and then into
`IsPaper2ClassicalSolution`. -/
theorem localExistence_of_coupledDuhamel_resolver_estimates_and_regularization
    (p : CM2Params)
    (R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {A L K T M : ℝ} (hA : 0 < A) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hT : 0 < T) (hAT : A * T < 1) (hM : 0 ≤ M)
    (hA_bound : |p.χ₀| * K + L ≤ A)
    (hL_lip : ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
      |a * (p.a - p.b * a ^ p.α) - b * (p.a - p.b * b ^ p.α)| ≤
        L * |a - b|)
    (hest : IntervalCoupledResolverBallEstimates p R u₀ T M K)
    (hregularize :
      ∀ u v : ℝ → intervalDomainPoint → ℝ,
        intervalTrajectoryBoundedOn T M u →
        (∀ t x, 0 ≤ t → t ≤ T →
          u t x = intervalCoupledDuhamelOperator p R u₀ u t x) →
        (∀ t, v t = R (u t)) →
          RegularityBootstrap p T u₀ u) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  rcases hest with ⟨hmap, _hchem, _hint, _hlift_int⟩
  have hcontr :
      ∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
        0 ≤ D →
        intervalTrajectoryBoundedOn T M u₁ →
        intervalTrajectoryBoundedOn T M u₂ →
        (∀ s y, 0 ≤ s → s ≤ T → |u₁ s y - u₂ s y| ≤ D) →
        ∀ t x, 0 ≤ t → t ≤ T →
          |intervalCoupledDuhamelOperator p R u₀ u₁ t x -
            intervalCoupledDuhamelOperator p R u₀ u₂ t x| ≤ A * T * D :=
    intervalCoupledDuhamel_closedBall_contraction_of_resolver_estimates
      p R u₀ hT hL hK hA_bound hL_lip
      ⟨hmap, _hchem, _hint, _hlift_int⟩
  have hzero_ball :
      intervalTrajectoryBoundedOn T M
        (fun _ : ℝ => fun _ : intervalDomainPoint => 0) := by
    intro t x _ht0 _htT
    simpa using hM
  have hbase :
      ∀ t x, 0 ≤ t → t ≤ T →
        |intervalCoupledDuhamelOperator p R u₀ (fun _ _ => 0) t x| ≤ M :=
    hmap (fun _ : ℝ => fun _ : intervalDomainPoint => 0) hzero_ball
  exact localExistence_of_coupledDuhamel_closedBall_contraction_and_regularization
    p R u₀ hu₀ hA hM hT hAT hM hmap hcontr hbase hregularize

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
    (hφ_deriv_cont : ContinuousOn (deriv φ) (Set.Ioo 0 T))
    (v : ℝ → intervalDomainPoint → ℝ)
    (hvC2 : ∀ t, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Ioo (0 : ℝ) 1))
    (hvTime : ∀ x : intervalDomainPoint,
      ∀ t, t ∈ Set.Ioo (0 : ℝ) T →
        DifferentiableAt ℝ (fun s : ℝ => v s x) t)
    (hvTimeCont : ∀ x : intervalDomainPoint,
      ContinuousOn (fun s : ℝ => deriv (fun r : ℝ => v r x) s)
        (Set.Ioo (0 : ℝ) T))
    (hvTimeJoint : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (v s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1))
    (hvNeumann : ∀ t, t ∈ Set.Ioo (0 : ℝ) T →
      Filter.Tendsto (deriv (intervalDomainLift (v t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (deriv (intervalDomainLift (v t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hvC2Icc : ∀ t, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) ∧
        deriv (intervalDomainLift (v t)) 0 = 0 ∧
        deriv (intervalDomainLift (v t)) 1 = 0)
    (hvTimeJointIcc : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s : ℝ => intervalDomainLift (v s) x) t))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1))
    (hvFieldJoint : ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    intervalDomainClassicalRegularity T
      (fun t (_ : intervalDomainPoint) => φ t) v := by
  unfold intervalDomainClassicalRegularity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) spatial C² regularity on (0,1).  `u t = fun _ => φ t`
    -- is spatially constant; `v` is C² by hypothesis.
    intro t ht
    exact ⟨intervalDomainLift_const_contDiffOn (φ t), hvC2 t ht⟩
  · -- Fourth conjunct: interior time `C¹`.  `s ↦ u s x = φ s` is differentiable
    -- on `(0,T)` by `hφ_diff` (open set ⇒ `DifferentiableAt`) with `∂ₜ = deriv φ`
    -- continuous (`hφ_deriv_cont`); `s ↦ v s x` is supplied by `hvTime`/`hvTimeCont`.
    intro x t ht
    refine ⟨⟨(hφ_diff t ht).differentiableAt (isOpen_Ioo.mem_nhds ht),
      hvTime x t ht⟩, hφ_deriv_cont, hvTimeCont x⟩
  · -- Fifth conjunct: JOINT space-time continuity of `∂ₜ`.  For `u t = fun _ => φ t`
    -- the lift at any interior `x ∈ (0,1) ⊆ [0,1]` equals `φ t`, so `∂ₜ` of the
    -- time slice is `deriv φ t`, independent of `x` and continuous in `t`; hence
    -- jointly continuous via composition with the first projection.  `v` is
    -- supplied jointly by hypothesis.
    refine ⟨?_, hvTimeJoint⟩
    have hEq : Set.EqOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ =>
              intervalDomainLift ((fun t (_ : intervalDomainPoint) => φ t) s) x) t))
        (fun q : ℝ × ℝ => deriv φ q.1)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) := by
      rintro ⟨t, x⟩ ⟨_ht, hx⟩
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
      have hslice : (fun s : ℝ =>
          intervalDomainLift ((fun t (_ : intervalDomainPoint) => φ t) s) x)
          = fun s : ℝ => φ s := by
        funext s; simp [intervalDomainLift, hxIcc]
      simp only [Function.uncurry]
      rw [hslice]
    refine ContinuousOn.congr ?_ hEq
    exact hφ_deriv_cont.comp continuousOn_fst (fun q hq => hq.1)
  · -- Sixth conjunct: genuine interior-Neumann.  `u t = fun _ => φ t` is
    -- spatially constant (lift deriv vanishes on `(0,1)`); `v` is supplied.
    intro t ht
    exact ⟨intervalDomainLift_const_neumann (φ t), hvNeumann t ht⟩
  · -- Seventh conjunct: CLOSED-`Icc` spatial `C²` + endpoint Neumann.  `u t` is
    -- spatially constant; `v` is supplied by `hvC2Icc`.
    intro t ht
    exact ⟨⟨intervalDomainLift_const_contDiffOn_Icc (φ t),
            (intervalDomainLift_const_deriv_endpoint_zero (φ t)).1,
            (intervalDomainLift_const_deriv_endpoint_zero (φ t)).2⟩,
           hvC2Icc t ht⟩
  · -- Eighth conjunct: CLOSED-slab joint `∂ₜ` continuity.  For `u t = fun _ => φ t`
    -- the lift at any `x ∈ [0,1]` equals `φ t`, so `∂ₜ` of the time slice is
    -- `deriv φ t`, continuous in `t` ⇒ jointly continuous on `Ioo 0 T ×ˢ Icc 0 1`.
    refine ⟨?_, hvTimeJointIcc⟩
    have hEq : Set.EqOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ =>
              intervalDomainLift ((fun t (_ : intervalDomainPoint) => φ t) s) x) t))
        (fun q : ℝ × ℝ => deriv φ q.1)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
      rintro ⟨t, x⟩ ⟨_ht, hxIcc⟩
      have hslice : (fun s : ℝ =>
          intervalDomainLift ((fun t (_ : intervalDomainPoint) => φ t) s) x)
          = fun s : ℝ => φ s := by
        funext s; simp [intervalDomainLift, hxIcc]
      simp only [Function.uncurry]
      rw [hslice]
    refine ContinuousOn.congr ?_ hEq
    exact hφ_deriv_cont.comp continuousOn_fst (fun q hq => hq.1)
  · -- Ninth conjunct (R1): CLOSED-slab joint SOLUTION-field continuity.  For
    -- `u t = fun _ => φ t` the lift at any `x ∈ [0,1]` equals `φ t`, so the
    -- solution field equals `(t,x) ↦ φ t`, jointly continuous via composition of
    -- `hφ_cont` with the first projection.  `v` is supplied by `hvFieldJoint`.
    refine ⟨?_, hvFieldJoint⟩
    have hEq : Set.EqOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift ((fun t (_ : intervalDomainPoint) => φ t) t) x))
        (fun q : ℝ × ℝ => φ q.1)
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
      rintro ⟨t, x⟩ ⟨_ht, hxIcc⟩
      simp only [Function.uncurry]
      simp [intervalDomainLift, hxIcc]
    refine ContinuousOn.congr ?_ hEq
    exact (hφ_cont.mono Set.Ioo_subset_Icc_self).comp continuousOn_fst
      (fun q hq => hq.1)

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
  refine ⟨fun t _ => ellipticV p (φ t), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Positivity
    exact fun _t _x _ht0 _htT => hφ_pos _
  · -- v-nonnegativity
    exact fun t _x _ht0 _htT => (ellipticV_pos p (hφ_pos t)).le
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
    -- `s ↦ ellipticV p (φ s) = (ν/μ) * (φ s) ^ γ` is differentiable in `s`:
    -- `φ` is differentiable on the open `(0,T)` and stays positive, so the real
    -- power composes differentiably.
    have hvDiff : ∀ x : intervalDomainPoint,
        ∀ t, t ∈ Set.Ioo (0 : ℝ) T →
          DifferentiableAt ℝ (fun s : ℝ => ellipticV p (φ s)) t := by
      intro x t ht
      have hφ_at : DifferentiableAt ℝ φ t :=
        (hφ_diff t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
      have hpow : DifferentiableAt ℝ (fun s : ℝ => (φ s) ^ p.γ) t := by
        have := (Real.differentiableAt_rpow_const_of_ne (p.γ) (ne_of_gt (hφ_pos t)))
        exact this.comp t hφ_at
      have : DifferentiableAt ℝ (fun s : ℝ => (p.ν / p.μ) * (φ s) ^ p.γ) t :=
        hpow.const_mul (p.ν / p.μ)
      simpa [ellipticV] using this
    -- Continuity of `∂ₜφ = deriv φ` on `(0,T)`: by the ODE, `deriv φ` agrees on
    -- `(0,T)` with `t ↦ φ t * (a − b (φ t)^α)`, continuous since `φ` is
    -- continuous on the open `(0,T)` and stays positive.
    have hφ_cont_Ioo : ContinuousOn φ (Set.Ioo 0 T) :=
      fun t ht => ((hφ_diff t ht).differentiableAt
        (isOpen_Ioo.mem_nhds ht)).continuousAt.continuousWithinAt
    have hφ_pow_cont : ContinuousOn (fun t : ℝ => (φ t) ^ p.α) (Set.Ioo 0 T) := by
      apply ContinuousOn.rpow_const hφ_cont_Ioo
      exact fun t _ => Or.inl (ne_of_gt (hφ_pos t))
    have hφ_deriv_cont : ContinuousOn (deriv φ) (Set.Ioo 0 T) := by
      refine ContinuousOn.congr ?_ (fun t ht => hφ_ode t ht)
      exact hφ_cont_Ioo.mul (continuousOn_const.sub
        (continuousOn_const.mul hφ_pow_cont))
    -- Continuity of `∂ₜ(ellipticV ∘ φ)` on `(0,T)`.  On the open `(0,T)` the
    -- chain rule gives `∂ₜ ((ν/μ)(φ)^γ) = (ν/μ) γ (φ)^{γ−1} φ'`, continuous since
    -- `φ`, `φ'` are continuous and `φ > 0`.
    have hellipticDerivCont :
        ContinuousOn (fun s : ℝ => deriv (fun r : ℝ => ellipticV p (φ r)) s)
          (Set.Ioo (0 : ℝ) T) := by
      have hpowDeriv : Set.EqOn
          (fun s : ℝ => deriv (fun r : ℝ => ellipticV p (φ r)) s)
          (fun s : ℝ => (p.ν / p.μ) * (p.γ * (φ s) ^ (p.γ - 1) * deriv φ s))
          (Set.Ioo (0 : ℝ) T) := by
        intro s hs
        have hφ_at : DifferentiableAt ℝ φ s :=
          (hφ_diff s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)
        have hrpow : HasDerivAt (fun r : ℝ => (φ r) ^ p.γ)
            (deriv φ s * p.γ * (φ s) ^ (p.γ - 1)) s :=
          hφ_at.hasDerivAt.rpow_const (Or.inl (ne_of_gt (hφ_pos s)))
        have hev : HasDerivAt (fun r : ℝ => ellipticV p (φ r))
            ((p.ν / p.μ) * (p.γ * (φ s) ^ (p.γ - 1) * deriv φ s)) s := by
          have := (hrpow.const_mul (p.ν / p.μ))
          simpa [ellipticV, mul_comm, mul_left_comm, mul_assoc] using this
        exact hev.deriv
      refine ContinuousOn.congr ?_ hpowDeriv
      have hφ_pow1_cont : ContinuousOn (fun s : ℝ => (φ s) ^ (p.γ - 1))
          (Set.Ioo 0 T) := by
        apply ContinuousOn.rpow_const hφ_cont_Ioo
        exact fun s _ => Or.inl (ne_of_gt (hφ_pos s))
      exact continuousOn_const.mul
        ((continuousOn_const.mul hφ_pow1_cont).mul hφ_deriv_cont)
    -- Joint continuity of `∂ₜ` of the `v`-slice.  `v s = fun _ => ellipticV p (φ s)`
    -- is spatially constant, so its lift at any interior `x ∈ (0,1) ⊆ [0,1]` equals
    -- `ellipticV p (φ s)`, hence `∂ₜ` depends only on `t` and is continuous via the
    -- single-variable `hellipticDerivCont` composed with the first projection.
    have hvJoint : ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ =>
              intervalDomainLift
                ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) := by
      have hEq : Set.EqOn
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ =>
                intervalDomainLift
                  ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) s) x) t))
          (fun q : ℝ × ℝ => deriv (fun r : ℝ => ellipticV p (φ r)) q.1)
          (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) 1) := by
        rintro ⟨t, x⟩ ⟨_ht, hx⟩
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
        have hslice : (fun s : ℝ =>
            intervalDomainLift
              ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) s) x)
            = fun s : ℝ => ellipticV p (φ s) := by
          funext s; simp [intervalDomainLift, hxIcc]
        simp only [Function.uncurry]
        rw [hslice]
      refine ContinuousOn.congr ?_ hEq
      exact hellipticDerivCont.comp continuousOn_fst (fun q hq => hq.1)
    -- Closed-slab joint `∂ₜ` continuity for the (spatially constant) `v`-slice.
    have hvJointIcc : ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s : ℝ =>
              intervalDomainLift
                ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) s) x) t))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
      have hEq : Set.EqOn
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) =>
              deriv (fun s : ℝ =>
                intervalDomainLift
                  ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) s) x) t))
          (fun q : ℝ × ℝ => deriv (fun r : ℝ => ellipticV p (φ r)) q.1)
          (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
        rintro ⟨t, x⟩ ⟨_ht, hxIcc⟩
        have hslice : (fun s : ℝ =>
            intervalDomainLift
              ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) s) x)
            = fun s : ℝ => ellipticV p (φ s) := by
          funext s; simp [intervalDomainLift, hxIcc]
        simp only [Function.uncurry]
        rw [hslice]
      refine ContinuousOn.congr ?_ hEq
      exact hellipticDerivCont.comp continuousOn_fst (fun q hq => hq.1)
    -- (R1) Closed-slab joint SOLUTION-field continuity for the (spatially
    -- constant) `v`-slice: the field equals `(t,x) ↦ ellipticV p (φ t)`,
    -- continuous via `t ↦ (ν/μ)(φ t)^γ` composed with the first projection.
    have hellipticCont : ContinuousOn (fun s : ℝ => ellipticV p (φ s))
        (Set.Ioo (0 : ℝ) T) := by
      have hφ_pow_g : ContinuousOn (fun s : ℝ => (φ s) ^ p.γ) (Set.Ioo 0 T) := by
        apply ContinuousOn.rpow_const hφ_cont_Ioo
        exact fun s _ => Or.inl (ne_of_gt (hφ_pos s))
      have : ContinuousOn (fun s : ℝ => (p.ν / p.μ) * (φ s) ^ p.γ)
          (Set.Ioo 0 T) := continuousOn_const.mul hφ_pow_g
      simpa [ellipticV] using this
    have hvFieldJoint : ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            intervalDomainLift
              ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) t) x))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
      have hEq : Set.EqOn
          (Function.uncurry
            (fun (t : ℝ) (x : ℝ) =>
              intervalDomainLift
                ((fun t (_ : intervalDomainPoint) => ellipticV p (φ t)) t) x))
          (fun q : ℝ × ℝ => ellipticV p (φ q.1))
          (Set.Ioo (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
        rintro ⟨t, x⟩ ⟨_ht, hxIcc⟩
        simp only [Function.uncurry]
        simp [intervalDomainLift, hxIcc]
      refine ContinuousOn.congr ?_ hEq
      exact hellipticCont.comp continuousOn_fst (fun q hq => hq.1)
    refine classicalRegularity_of_spatially_constant_decreasing hT hφ_pos
      hφ_cont hφ_diff hφ_deriv_nonpos hφ_deriv_cont _
      (fun t _ht => intervalDomainLift_const_contDiffOn (ellipticV p (φ t)))
      hvDiff (fun x => hellipticDerivCont) hvJoint
      (fun t _ht => intervalDomainLift_const_neumann (ellipticV p (φ t)))
      (fun t _ht => ⟨intervalDomainLift_const_contDiffOn_Icc (ellipticV p (φ t)),
        (intervalDomainLift_const_deriv_endpoint_zero (ellipticV p (φ t))).1,
        (intervalDomainLift_const_deriv_endpoint_zero (ellipticV p (φ t))).2⟩)
      hvJointIcc hvFieldJoint
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
  simp only [h, and_false, ↓reduceDIte]

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
  change intervalDomainSupNorm (u t) ≤ intervalDomainSupNorm u₀ + ε
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

/-! ### Theorem 1.1 existence-package bridge

The Theorem 1.1 bridge consumes
`Paper2.IntervalDomainTheorem11.IntervalDomainExistence p`.  That package has
three fields: local existence, initial sup-norm approach, and a global-extension
criterion.  The concrete `InitialTrace` theorem above discharges the initial
approach field once admissible initial data are known to be sup-norm bounded.

The global-extension field is stronger than a usual maximal-continuation
statement: it requires the same already-given functions `u, v` to be global,
not merely the existence of a continued/glued global solution.  The diagnostic
below records this semantic frontier. -/

/-- Assemble the Theorem 1.1 interval-domain existence package from local
existence, bounded admissible initial data, and the global-extension criterion.

This is the concrete version of the bridge needed by Theorem 1.1: the
`initialSupNormApproach` field is proved in this file from `InitialTrace`; the
remaining two inputs are the genuine Cauchy/maximal-continuation fields. -/
theorem intervalDomainTheorem11Existence_of_local_global_bounded_initial
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    Paper2.IntervalDomainTheorem11.IntervalDomainExistence p := by
  refine
    { localExistence := hlocal
      initialSupNormApproach := ?_
      globalExtension := hglobal }
  intro u₀ hu₀ T hT u v hsol htrace ε hε
  exact initialSupNormApproach_intervalDomain p u₀ hu₀
    (hboundedInitial u₀ hu₀) hT hsol htrace hε

/-- The concrete Duhamel/Picard local-existence branch supplies the
`localExistence` field of the Theorem 1.1 package.  The remaining inputs are
exactly the two fields not provided by the local fixed-point construction:
bounded admissible initial data and the global-extension criterion. -/
theorem intervalDomainTheorem11Existence_of_intervalDuhamel_contraction_regularization
    (p : CM2Params)
    (hmild :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ L > 0, ∃ D₀ ≥ 0, ∃ T > 0,
            L * T < 1 ∧
            (∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
              0 ≤ D →
              (∀ s y, 0 ≤ s → s ≤ T →
                |u₁ s y - u₂ s y| ≤ D) →
              ∀ t x, 0 ≤ t → t ≤ T →
                |intervalDuhamelOperator p u₀ u₁ t x -
                  intervalDuhamelOperator p u₀ u₂ t x| ≤ L * T * D) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ D₀) ∧
            (∀ u : ℝ → intervalDomainPoint → ℝ,
              (∀ t x, 0 ≤ t → t ≤ T →
                u t x = intervalDuhamelOperator p u₀ u t x) →
                RegularityBootstrap p T u₀ u))
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    Paper2.IntervalDomainTheorem11.IntervalDomainExistence p := by
  exact intervalDomainTheorem11Existence_of_local_global_bounded_initial p
    (intervalDomain_localExistence_of_intervalDuhamel_contraction_regularization
      p hmild)
    hboundedInitial hglobal

/-- General bad-tail obstruction to the current Theorem 1.1 `globalExtension`
field.

Reason: the field quantifies over every pair of functions `u, v` that solves on
the finite horizon and then concludes that the same functions are global.  A
solution can be changed after the finite horizon without affecting the finite
horizon hypotheses.  Here `u` is a positive constant state satisfying the
reaction balance, while `v` is the correct elliptic value before `t = 1` and
zero afterwards.  It solves on `(0,1)`, has the correct initial trace and
boundedness, but cannot be a global classical solution. -/
theorem not_intervalDomainTheorem11_globalExtension_constant_bad_tail
    (p : CM2Params) {c : ℝ} (hc : 0 < c)
    (hreact : p.a - p.b * c ^ p.α = 0) (hm : 1 ≤ p.m) :
    ¬ (∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v) := by
  intro hglobal
  let u : ℝ → intervalDomain.Point → ℝ := fun _ _ => c
  let v : ℝ → intervalDomain.Point → ℝ :=
    fun t _ => if t < 1 then ellipticV p c else 0
  have hu₀ : PositiveInitialDatum intervalDomain (constOnInterval c) :=
    constOnInterval_pos hc
  have htrace : InitialTrace intervalDomain (constOnInterval c) u := by
    dsimp [u]
    exact constantSolution_initialTrace c
  have hbounded : IsPaper2BoundedBefore intervalDomain (1 : ℝ) u := by
    refine ⟨c, ?_⟩
    intro t _ht0 _htT
    dsimp [u]
    change intervalDomainSupNorm (fun _ : intervalDomainPoint => c) ≤ c
    rw [intervalDomainSupNorm_const, abs_of_pos hc]
  have hsol : IsPaper2ClassicalSolution intervalDomain p 1 u v := by
    refine IsPaper2ClassicalSolution.of_components one_pos ?_ ?_ ?_ ?_ ?_ ?_
    · -- Regularity for `u ≡ c`, `v t = if t < 1 then ellipticV p c else 0`.
      -- The sup-norm conjuncts depend only on `u`; the C² conjunct needs the
      -- lift of `v t` on `(0,1)`, where `t < 1` forces `v t = fun _ => ellipticV p c`.
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro t ht
        have hvt : v t = fun _ : intervalDomainPoint => ellipticV p c := by
          funext y
          show (if t < 1 then ellipticV p c else 0) = ellipticV p c
          rw [if_pos ht.2]
        refine ⟨intervalDomainLift_const_contDiffOn c, ?_⟩
        rw [hvt]
        exact intervalDomainLift_const_contDiffOn (ellipticV p c)
      · -- Fourth conjunct: `s ↦ u s x = c` is constant; `s ↦ v s x` equals the
        -- constant `ellipticV p c` on the neighborhood `Iio 1 ∋ t`, hence is
        -- differentiable at every `t ∈ (0,1)`.
        intro x t ht
        -- `v s x = ellipticV p c` for all `s < 1`, in particular near any
        -- `t ∈ (0,1)` and on the whole `(0,1)`.
        have hvEqOn : Set.EqOn (fun s : ℝ => v s x)
            (fun _ : ℝ => ellipticV p c) (Set.Iio (1 : ℝ)) := by
          intro s hs
          show (if s < 1 then ellipticV p c else 0) = ellipticV p c
          rw [if_pos (Set.mem_Iio.mp hs)]
        have hdiffV : DifferentiableAt ℝ (fun s : ℝ => v s x) t := by
          have hev : (fun s : ℝ => v s x) =ᶠ[nhds t]
              (fun _ : ℝ => ellipticV p c) :=
            Set.EqOn.eventuallyEq_of_mem hvEqOn (isOpen_Iio.mem_nhds ht.2)
          exact (hev.differentiableAt_iff).mpr (differentiableAt_const _)
        refine ⟨⟨differentiableAt_const c, hdiffV⟩, ?_, ?_⟩
        · -- `∂ₜu = deriv (fun _ => c) = 0`, continuous on `(0,1)`.
          have : (fun s : ℝ => deriv (fun _r : ℝ => c) s) = fun _ => (0 : ℝ) := by
            ext s; exact deriv_const s c
          rw [this]; exact continuousOn_const
        · -- `∂ₜv = 0` on `(0,1)` since `v · x` is locally constant there.
          have hderiv0 : Set.EqOn (fun s : ℝ => deriv (fun r : ℝ => v r x) s)
              (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
            intro s hs
            have hev : (fun r : ℝ => v r x) =ᶠ[nhds s]
                (fun _ : ℝ => ellipticV p c) :=
              Set.EqOn.eventuallyEq_of_mem hvEqOn (isOpen_Iio.mem_nhds hs.2)
            simp only [hev.deriv_eq, deriv_const]
          exact continuousOn_const.congr hderiv0
      · -- Fifth conjunct: JOINT space-time continuity of `∂ₜ` on `(0,1) × (0,1)`.
        -- `u ≡ c` has lift constant in time (`∂ₜ ≡ 0`).  For `v`, at any interior
        -- `t ∈ (0,1)` the slice `s ↦ lift(v s) x = (if s < 1 then ellipticV p c
        -- else 0)` is locally constant near `t` (since `t < 1`), so `∂ₜ ≡ 0` on
        -- the slab; both fields are identically `0`, hence jointly continuous.
        constructor
        · have h0 : Set.EqOn
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) =>
                  deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
              (fun _ : ℝ × ℝ => (0 : ℝ))
              (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
            rintro ⟨t, x⟩ _
            simp only [Function.uncurry]
            show deriv (fun s : ℝ => intervalDomainLift (u s) x) t = 0
            have : (fun s : ℝ => intervalDomainLift (u s) x)
                = fun _ : ℝ => intervalDomainLift (fun _ : intervalDomainPoint => c) x := by
              funext s; rfl
            rw [this, deriv_const]
          exact continuousOn_const.congr h0
        · have h0 : Set.EqOn
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) =>
                  deriv (fun s : ℝ => intervalDomainLift (v s) x) t))
              (fun _ : ℝ × ℝ => (0 : ℝ))
              (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
            rintro ⟨t, x⟩ ⟨ht, hx⟩
            simp only [Function.uncurry]
            show deriv (fun s : ℝ => intervalDomainLift (v s) x) t = 0
            have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
            have hslice : (fun s : ℝ => intervalDomainLift (v s) x)
                =ᶠ[nhds t] (fun _ : ℝ => ellipticV p c) := by
              refine Set.EqOn.eventuallyEq_of_mem ?_ (isOpen_Iio.mem_nhds ht.2)
              intro s hs
              show intervalDomainLift (v s) x = ellipticV p c
              simp only [intervalDomainLift, hxIcc, dif_pos]
              show (if s < 1 then ellipticV p c else 0) = ellipticV p c
              rw [if_pos (Set.mem_Iio.mp hs)]
            rw [hslice.deriv_eq, deriv_const]
          exact continuousOn_const.congr h0
      · -- Sixth conjunct: genuine interior-Neumann.  `u ≡ c` and (on `(0,1)`)
        -- `v t = ellipticV p c` are both spatially constant.
        intro t ht
        have hvt : v t = fun _ : intervalDomainPoint => ellipticV p c := by
          funext y
          show (if t < 1 then ellipticV p c else 0) = ellipticV p c
          rw [if_pos ht.2]
        refine ⟨intervalDomainLift_const_neumann c, ?_⟩
        rw [hvt]
        exact intervalDomainLift_const_neumann (ellipticV p c)
      · -- Seventh conjunct: CLOSED-`Icc` `C²` + endpoint Neumann.  `u ≡ c`; on
        -- `(0,1)` we have `v t = ellipticV p c`, both spatially constant.
        intro t ht
        have hvt : v t = fun _ : intervalDomainPoint => ellipticV p c := by
          funext y
          show (if t < 1 then ellipticV p c else 0) = ellipticV p c
          rw [if_pos ht.2]
        refine ⟨⟨intervalDomainLift_const_contDiffOn_Icc c,
                 (intervalDomainLift_const_deriv_endpoint_zero c).1,
                 (intervalDomainLift_const_deriv_endpoint_zero c).2⟩, ?_⟩
        rw [hvt]
        exact ⟨intervalDomainLift_const_contDiffOn_Icc (ellipticV p c),
               (intervalDomainLift_const_deriv_endpoint_zero (ellipticV p c)).1,
               (intervalDomainLift_const_deriv_endpoint_zero (ellipticV p c)).2⟩
      · -- Eighth conjunct: CLOSED-slab joint `∂ₜ` continuity on `(0,1) ×ˢ Icc 0 1`.
        -- `u ≡ c` ⇒ `∂ₜ ≡ 0`; `v` is locally constant near each `t < 1`.
        constructor
        · have h0 : Set.EqOn
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) =>
                  deriv (fun s : ℝ => intervalDomainLift (u s) x) t))
              (fun _ : ℝ × ℝ => (0 : ℝ))
              (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
            rintro ⟨t, x⟩ _
            simp only [Function.uncurry]
            show deriv (fun s : ℝ => intervalDomainLift (u s) x) t = 0
            have : (fun s : ℝ => intervalDomainLift (u s) x)
                = fun _ : ℝ => intervalDomainLift (fun _ : intervalDomainPoint => c) x := by
              funext s; rfl
            rw [this, deriv_const]
          exact continuousOn_const.congr h0
        · have h0 : Set.EqOn
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) =>
                  deriv (fun s : ℝ => intervalDomainLift (v s) x) t))
              (fun _ : ℝ × ℝ => (0 : ℝ))
              (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
            rintro ⟨t, x⟩ ⟨ht, hxIcc⟩
            simp only [Function.uncurry]
            show deriv (fun s : ℝ => intervalDomainLift (v s) x) t = 0
            have hslice : (fun s : ℝ => intervalDomainLift (v s) x)
                =ᶠ[nhds t] (fun _ : ℝ => ellipticV p c) := by
              refine Set.EqOn.eventuallyEq_of_mem ?_ (isOpen_Iio.mem_nhds ht.2)
              intro s hs
              show intervalDomainLift (v s) x = ellipticV p c
              simp only [intervalDomainLift, hxIcc, dif_pos]
              show (if s < 1 then ellipticV p c else 0) = ellipticV p c
              rw [if_pos (Set.mem_Iio.mp hs)]
            rw [hslice.deriv_eq, deriv_const]
          exact continuousOn_const.congr h0
      · -- Ninth conjunct (R1): CLOSED-slab joint SOLUTION-field continuity on
        -- `(0,1) ×ˢ Icc 0 1`.  `u ≡ c` ⇒ field `= c`; on the slab `t < 1` so
        -- `v t = ellipticV p c` ⇒ field `= ellipticV p c`, both constant hence
        -- jointly continuous.
        constructor
        · have h0 : Set.EqOn
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
              (fun _ : ℝ × ℝ => c)
              (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
            rintro ⟨t, x⟩ ⟨_ht, hxIcc⟩
            simp only [Function.uncurry]
            show intervalDomainLift (fun _ : intervalDomainPoint => c) x = c
            simp [intervalDomainLift, hxIcc]
          exact continuousOn_const.congr h0
        · have h0 : Set.EqOn
              (Function.uncurry
                (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
              (fun _ : ℝ × ℝ => ellipticV p c)
              (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
            rintro ⟨t, x⟩ ⟨ht, hxIcc⟩
            simp only [Function.uncurry]
            show intervalDomainLift (v t) x = ellipticV p c
            simp only [intervalDomainLift, hxIcc, dif_pos]
            show (if t < 1 then ellipticV p c else 0) = ellipticV p c
            rw [if_pos ht.2]
          exact continuousOn_const.congr h0
    · intro _t _x _ht0 _htT
      exact hc
    · -- v-nonnegativity: `v t x = if t<1 then ellipticV p c else 0`, both ≥ 0.
      intro t x _ht0 _htT
      change (0:ℝ) ≤ (if t < 1 then ellipticV p c else 0)
      have hev : (0:ℝ) ≤ ellipticV p c := (ellipticV_pos p hc).le
      split <;> simp [hev]
    · intro t x _ht0 htT hx
      have hv_t : v t = fun _ : intervalDomain.Point => ellipticV p c := by
        ext y
        simp [v, htT]
      change deriv (fun _s : ℝ => c) t =
        intervalDomainLaplacian (fun _ => c) x
          - p.χ₀ * intervalDomainChemotaxisDiv p (fun _ => c) (v t) x
          + c * (p.a - p.b * c ^ p.α)
      rw [hv_t, deriv_const, intervalDomainLaplacian_const_zero c hx]
      change (0 : ℝ) =
        0 - p.χ₀ * intervalDomainChemotaxisDiv p
          (fun _ : intervalDomainPoint => c)
          (fun _ : intervalDomainPoint => ellipticV p c) x
          + c * (p.a - p.b * c ^ p.α)
      have hchem :
          intervalDomainChemotaxisDiv p (fun _ : intervalDomainPoint => c)
            (fun _ : intervalDomainPoint => ellipticV p c) x = 0 :=
        intervalDomainChemotaxisDiv_const_zero p c (ellipticV p c) hx
      have hchem_mul :
          p.χ₀ * intervalDomainChemotaxisDiv p
            (fun _ : intervalDomainPoint => c)
            (fun _ : intervalDomainPoint => ellipticV p c) x = 0 := by
        rw [hchem, mul_zero]
      have hreact_mul : c * (p.a - p.b * c ^ p.α) = 0 := by
        rw [hreact, mul_zero]
      nlinarith [hchem_mul, hreact_mul]
    · intro t x _ht0 htT hx
      have hv_t : v t = fun _ : intervalDomain.Point => ellipticV p c := by
        ext y
        simp [v, htT]
      change (0 : ℝ) =
        intervalDomainLaplacian (v t) x
          - p.μ * v t x + p.ν * c ^ p.γ
      rw [hv_t]
      exact ellipticV_pde p c hc hx
    · intro t x _ht0 htT hx
      have hv_t : v t = fun _ : intervalDomain.Point => ellipticV p c := by
        ext y
        simp [v, htT]
      change intervalDomainNormalDeriv (fun _ => c) x = 0 ∧
        intervalDomainNormalDeriv (v t) x = 0
      rw [hv_t]
      exact ⟨intervalDomainNormalDeriv_const_zero c hx,
        intervalDomainNormalDeriv_const_zero (ellipticV p c) hx⟩
  have hglob :
      IsPaper2GlobalClassicalSolution intervalDomain p u v :=
    hglobal (constOnInterval c) hu₀ 1 one_pos u v hsol htrace hbounded hm
  let xmid : intervalDomain.Point :=
    ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hxmid : xmid ∈ intervalDomain.inside := by
    change ((1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    constructor <;> norm_num
  have hpde_v :=
    (hglob 2 (by norm_num : (0 : ℝ) < 2)).pde_v
      (t := (3 / 2 : ℝ)) (x := xmid)
      (by norm_num) (by norm_num) hxmid
  have hnot_lt : ¬ (3 / 2 : ℝ) < 1 := by norm_num
  change (0 : ℝ) =
    intervalDomainLaplacian (v (3 / 2 : ℝ)) xmid
      - p.μ * v (3 / 2 : ℝ) xmid + p.ν * (u (3 / 2 : ℝ) xmid) ^ p.γ at hpde_v
  simp only [u, v, hnot_lt, if_false] at hpde_v
  have hlap_zero :
      intervalDomainLaplacian (fun _ : intervalDomain.Point => (0 : ℝ)) xmid = 0 :=
    intervalDomainLaplacian_const_zero (0 : ℝ) hxmid
  have hsource_pos : 0 < p.ν * c ^ p.γ :=
    mul_pos p.hν (Real.rpow_pos_of_pos hc _)
  nlinarith

/-- The current Theorem 1.1 `globalExtension` field cannot be proved as stated
for positive equilibrium parameters with `1 ≤ m`. -/
theorem not_intervalDomainTheorem11_globalExtension_equilibrium_bad_tail
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m) :
    ¬ (∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v) := by
  exact not_intervalDomainTheorem11_globalExtension_constant_bad_tail
    p (equilibrium_pos p ha hb) (equilibrium_reaction_zero p ha hb) hm

/-- Consequently the full Theorem 1.1 existence package is false for such
parameters with the current `globalExtension` field.  A standard
maximal-continuation theorem can provide a continued/glued global solution, or
a global/finite alternative, but not global regularity of arbitrary functions
after an unrelated finite horizon. -/
theorem not_intervalDomainTheorem11Existence_equilibrium_bad_tail
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) (hm : 1 ≤ p.m) :
    ¬ Paper2.IntervalDomainTheorem11.IntervalDomainExistence p := by
  intro hexist
  exact not_intervalDomainTheorem11_globalExtension_equilibrium_bad_tail
    p ha hb hm hexist.globalExtension

/-- The same bad-tail obstruction also hits the zero-reaction branch
`a = 0`, `b = 0`: any positive constant state has zero reaction, so the finite
horizon solution can again be modified after the horizon. -/
theorem not_intervalDomainTheorem11_globalExtension_zeroReaction_bad_tail
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hm : 1 ≤ p.m) :
    ¬ (∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v) := by
  refine not_intervalDomainTheorem11_globalExtension_constant_bad_tail
    p (c := 1) one_pos ?_ hm
  rw [ha, hb]
  ring

/-- Thus the full Theorem 1.1 existence package is also false in the minimal
zero-reaction branch when `1 ≤ m`, for the same same-tail reason. -/
theorem not_intervalDomainTheorem11Existence_zeroReaction_bad_tail
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) (hm : 1 ≤ p.m) :
    ¬ Paper2.IntervalDomainTheorem11.IntervalDomainExistence p := by
  intro hexist
  exact not_intervalDomainTheorem11_globalExtension_zeroReaction_bad_tail
    p ha hb hm hexist.globalExtension

/-- Concrete positive-logistic parameters witnessing that the current
`IntervalDomainExistence` interface cannot hold for all `CM2Params`. -/
def intervalDomainExistenceCounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 1
    b := 1
    β := 0
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

/-- The same-tail `globalExtension` field makes
`IntervalDomainExistence intervalDomainExistenceCounterParams` false. -/
theorem not_intervalDomainTheorem11Existence_counterParams :
    ¬ Paper2.IntervalDomainTheorem11.IntervalDomainExistence
      intervalDomainExistenceCounterParams := by
  exact not_intervalDomainTheorem11Existence_equilibrium_bad_tail
    intervalDomainExistenceCounterParams
    (by norm_num [intervalDomainExistenceCounterParams])
    (by norm_num [intervalDomainExistenceCounterParams])
    (by norm_num [intervalDomainExistenceCounterParams])

/-- Consequently there is no theorem of the form
`∀ p, IntervalDomainExistence p` for the current interface. -/
theorem not_forall_intervalDomainTheorem11Existence :
    ¬ ∀ p : CM2Params,
      Paper2.IntervalDomainTheorem11.IntervalDomainExistence p := by
  intro h
  exact not_intervalDomainTheorem11Existence_counterParams
    (h intervalDomainExistenceCounterParams)

/-! ### Corrected existential-global existence interface

The legacy `IntervalDomainTheorem11.IntervalDomainExistence` asks for the
arbitrary finite-horizon pair `u, v` itself to be global after `Tmax`; the
bad-tail theorems above show that this is false.  The corrected interface below
asks for existence of a genuine global pair with the same initial datum.  This
is the usual output of maximal continuation plus gluing/uniqueness. -/

/-- A genuine global interval-domain classical solution with the prescribed
initial trace. -/
def IntervalDomainGlobalSolutionFor
    (p : CM2Params) (u₀ : intervalDomain.Point → ℝ) : Prop :=
  ∃ u v : ℝ → intervalDomain.Point → ℝ,
    IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
    InitialTrace intervalDomain u₀ u

/-- Corrected Theorem 1.1 existence package: local existence and initial
sup-norm approach are as before, but the global component is existential.  It
does not require an arbitrary finite-horizon tail to be valid after its horizon. -/
structure IntervalDomainGlobalSolutionExists (p : CM2Params) where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  initialSupNormApproach :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ t, 0 < t → t < δ →
            intervalDomain.supNorm (u t) ≤ intervalDomain.supNorm u₀ + ε
  globalSolutionExists :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        1 ≤ p.m → IntervalDomainGlobalSolutionFor p u₀

/-- The corrected interface assembled from local existence, bounded initial
data, and a genuine existential global-continuation theorem. -/
theorem intervalDomainGlobalSolutionExists_of_local_global_bounded_initial
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          1 ≤ p.m → IntervalDomainGlobalSolutionFor p u₀) :
    IntervalDomainGlobalSolutionExists p := by
  refine
    { localExistence := hlocal
      initialSupNormApproach := ?_
      globalSolutionExists := hglobal }
  intro u₀ hu₀ T hT u v hsol htrace ε hε
  exact initialSupNormApproach_intervalDomain p u₀ hu₀
    (hboundedInitial u₀ hu₀) hT hsol htrace hε

/-- A gluing/uniqueness theorem converting arbitrarily long finite reachable
horizons into one global classical solution.  This is the analytic content that
prevents choosing unrelated solutions independently at each horizon. -/
def GlobalSolutionGluingFromReachability (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ReachableArbitrarilyLong p u₀ →
        IntervalDomainGlobalSolutionFor p u₀

/-! #### Gluing from overlap uniqueness

The order skeleton above gives one finite classical solution on every positive
horizon.  To turn those unrelated witnesses into one global solution, the first
real PDE input is overlap uniqueness: two interval-domain classical solutions
with the same initial trace must agree on the common time interval.  The lemmas
below prove the non-PDE part of the gluing argument from that uniqueness
frontier.
-/

/-- A packaged finite reachable classical solution on one horizon. -/
structure ReachableClassicalSolutionData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) where
  T_pos : 0 < T
  u : ℝ → intervalDomainPoint → ℝ
  v : ℝ → intervalDomainPoint → ℝ
  sol : IsPaper2ClassicalSolution intervalDomain p T u v
  trace : InitialTrace intervalDomain u₀ u

/-- Repackage the existing reachability predicate as structured data. -/
noncomputable def reachableClassicalSolutionDataOfReach
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hreach : ReachableClassicalHorizon p u₀ T) :
    ReachableClassicalSolutionData p u₀ T :=
  { T_pos := hreach.1
    u := Classical.choose hreach.2
    v := Classical.choose (Classical.choose_spec hreach.2)
    sol := (Classical.choose_spec (Classical.choose_spec hreach.2)).1
    trace := (Classical.choose_spec (Classical.choose_spec hreach.2)).2 }

/-- PDE uniqueness frontier needed for gluing: two finite interval solutions
with the same initial datum agree on the overlap of their horizons. -/
def IntervalClassicalSolutionOverlapUnique (p : CM2Params) : Prop :=
  ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ →
  ∀ {T₁ T₂ : ℝ}
    (d₁ : ReachableClassicalSolutionData p u₀ T₁)
    (d₂ : ReachableClassicalSolutionData p u₀ T₂),
      ∀ t, 0 < t → t < min T₁ T₂ →
        ∀ x : intervalDomainPoint, d₁.u t x = d₂.u t x ∧ d₁.v t x = d₂.v t x

/-- Datum-specific overlap uniqueness.  This is the faithful gluing interface
when the Cauchy theory is available only for a strengthened datum class (such
as the paper's uniformly positive data). -/
def IntervalClassicalSolutionOverlapUniqueAt
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ∀ {T₁ T₂ : ℝ}
    (d₁ : ReachableClassicalSolutionData p u₀ T₁)
    (d₂ : ReachableClassicalSolutionData p u₀ T₂),
      ∀ t, 0 < t → t < min T₁ T₂ →
        ∀ x : intervalDomainPoint, d₁.u t x = d₂.u t x ∧ d₁.v t x = d₂.v t x

theorem IntervalClassicalSolutionOverlapUnique.at
    {p : CM2Params} (h : IntervalClassicalSolutionOverlapUnique p)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    IntervalClassicalSolutionOverlapUniqueAt p u₀ :=
  h hu₀

/-- Locality frontier for the formal `IsPaper2ClassicalSolution` predicate:
if a candidate agrees pointwise with a known classical solution throughout
`(0,T)`, then it is itself a classical solution on `T`.

For the concrete interval domain this should follow from local equality and
`Filter.EventuallyEq` transport of time/spatial derivatives, plus transport of
the sup-norm regularity field.  It is kept explicit because it is a separate
calculus/locality layer from PDE uniqueness. -/
def ClassicalSolutionLocalityUnderIooAgreement (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v U V : ℝ → intervalDomainPoint → ℝ},
    0 < T →
      IsPaper2ClassicalSolution intervalDomain p T U V →
      (∀ t, 0 < t → t < T →
        ∀ x : intervalDomainPoint, u t x = U t x ∧ v t x = V t x) →
        IsPaper2ClassicalSolution intervalDomain p T u v

private lemma intervalDomainSupNormDerivativeNonposOn_congr_of_eqOn
    {u U : ℝ → intervalDomainPoint → ℝ} {I : Set ℝ}
    (hreg : IntervalDomainSupNormDerivativeNonposOn U I)
    (hEq : ∀ t ∈ I, u t = U t) :
    IntervalDomainSupNormDerivativeNonposOn u I := by
  have hsup_eq : Set.EqOn
      (fun t => intervalDomainSupNorm (u t))
      (fun t => intervalDomainSupNorm (U t)) I := by
    intro t ht
    change intervalDomainSupNorm (u t) = intervalDomainSupNorm (U t)
    exact congrArg intervalDomainSupNorm (hEq t ht)
  refine ⟨hreg.continuousOn.congr hsup_eq, ?_, ?_⟩
  · exact hreg.differentiableOn.congr
      (fun t ht => hsup_eq (x := t) (interior_subset ht))
  · intro t ht
    have hsup_eventually :
        (fun s => intervalDomainSupNorm (u s)) =ᶠ[nhds t]
          (fun s => intervalDomainSupNorm (U s)) :=
      Set.EqOn.eventuallyEq_of_mem
        (fun s hs => hsup_eq (x := s) (interior_subset hs))
        (isOpen_interior.mem_nhds ht)
    rw [Filter.EventuallyEq.deriv_eq hsup_eventually]
    exact hreg.deriv_nonpos t ht

private lemma intervalDomainClassicalRegularity_congr_Ioo
    {T : ℝ} {u v U V : ℝ → intervalDomainPoint → ℝ}
    (hreg : intervalDomainClassicalRegularity T U V)
    (hEq : ∀ t, 0 < t → t < T → u t = U t)
    (hEqV : ∀ t, 0 < t → t < T → v t = V t) :
    intervalDomainClassicalRegularity T u v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- First conjunct: lifts of `u t, v t` equal lifts of `U t, V t` (pointwise
    -- function equality lifts to equal extensions), so C² transfers verbatim.
    intro t ht
    have huL : intervalDomainLift (u t) = intervalDomainLift (U t) := by
      rw [hEq t ht.1 ht.2]
    have hvL : intervalDomainLift (v t) = intervalDomainLift (V t) := by
      rw [hEqV t ht.1 ht.2]
    rw [huL, hvL]
    exact hreg.1 t ht
  · -- Second conjunct: the time slices `s ↦ u s x` and `s ↦ U s x` agree on the
    -- open `(0,T)`, hence are `EventuallyEq` near each interior `t`, so
    -- differentiability transfers.
    intro x t ht
    have huEv : (fun s : ℝ => u s x) =ᶠ[nhds t] (fun s : ℝ => U s x) :=
      Set.EqOn.eventuallyEq_of_mem
        (fun s hs => by rw [hEq s hs.1 hs.2])
        (isOpen_Ioo.mem_nhds ht)
    have hvEv : (fun s : ℝ => v s x) =ᶠ[nhds t] (fun s : ℝ => V s x) :=
      Set.EqOn.eventuallyEq_of_mem
        (fun s hs => by rw [hEqV s hs.1 hs.2])
        (isOpen_Ioo.mem_nhds ht)
    obtain ⟨⟨hU, hV⟩, hcontU, hcontV⟩ := hreg.2.1 x t ht
    -- For the continuity of `∂ₜ`: on the open `(0,T)` the slices agree, and
    -- `deriv` at an interior point depends only on a neighbourhood, so the two
    -- time-derivative fields agree pointwise on `(0,T)`.
    have hderivEqU : Set.EqOn (fun s : ℝ => deriv (fun r : ℝ => u r x) s)
        (fun s : ℝ => deriv (fun r : ℝ => U r x) s) (Set.Ioo (0 : ℝ) T) := by
      intro s hs
      have hEv : (fun r : ℝ => u r x) =ᶠ[nhds s] (fun r : ℝ => U r x) :=
        Set.EqOn.eventuallyEq_of_mem
          (fun r hr => by rw [hEq r hr.1 hr.2]) (isOpen_Ioo.mem_nhds hs)
      simp only [hEv.deriv_eq]
    have hderivEqV : Set.EqOn (fun s : ℝ => deriv (fun r : ℝ => v r x) s)
        (fun s : ℝ => deriv (fun r : ℝ => V r x) s) (Set.Ioo (0 : ℝ) T) := by
      intro s hs
      have hEv : (fun r : ℝ => v r x) =ᶠ[nhds s] (fun r : ℝ => V r x) :=
        Set.EqOn.eventuallyEq_of_mem
          (fun r hr => by rw [hEqV r hr.1 hr.2]) (isOpen_Ioo.mem_nhds hs)
      simp only [hEv.deriv_eq]
    exact ⟨⟨(huEv.differentiableAt_iff).mpr hU,
        (hvEv.differentiableAt_iff).mpr hV⟩,
      hcontU.congr hderivEqU, hcontV.congr hderivEqV⟩
  · -- Fifth conjunct: JOINT time-derivative continuity transfers.  On the open
    -- `(0,T)` the lifts `lift(u s) = lift(U s)` (pointwise `u s = U s` lifts to
    -- equal extensions), so near each interior `t` the time slices agree and the
    -- joint derivative fields agree on the slab; `ContinuousOn.congr` transfers
    -- `hreg`'s joint continuity.
    obtain ⟨hjU, hjV⟩ := hreg.2.2.1
    have hliftEq : ∀ s, 0 < s → s < T →
        intervalDomainLift (u s) = intervalDomainLift (U s) := by
      intro s hs0 hsT; rw [hEq s hs0 hsT]
    have hliftEqV : ∀ s, 0 < s → s < T →
        intervalDomainLift (v s) = intervalDomainLift (V s) := by
      intro s hs0 hsT; rw [hEqV s hs0 hsT]
    refine ⟨ContinuousOn.congr hjU ?_, ContinuousOn.congr hjV ?_⟩
    · rintro ⟨t, x⟩ ⟨ht, _hx⟩
      simp only [Function.uncurry]
      have hEv : (fun s : ℝ => intervalDomainLift (u s) x) =ᶠ[nhds t]
          (fun s : ℝ => intervalDomainLift (U s) x) :=
        Set.EqOn.eventuallyEq_of_mem
          (fun s hs => by rw [hliftEq s hs.1 hs.2]) (isOpen_Ioo.mem_nhds ht)
      rw [hEv.deriv_eq]
    · rintro ⟨t, x⟩ ⟨ht, _hx⟩
      simp only [Function.uncurry]
      have hEv : (fun s : ℝ => intervalDomainLift (v s) x) =ᶠ[nhds t]
          (fun s : ℝ => intervalDomainLift (V s) x) :=
        Set.EqOn.eventuallyEq_of_mem
          (fun s hs => by rw [hliftEqV s hs.1 hs.2]) (isOpen_Ioo.mem_nhds ht)
      rw [hEv.deriv_eq]
  · -- Sixth conjunct: lifts of `u t, v t` equal lifts of `U t, V t`, so the
    -- one-sided endpoint derivative limits transfer verbatim.
    intro t ht
    have huL : intervalDomainLift (u t) = intervalDomainLift (U t) := by
      rw [hEq t ht.1 ht.2]
    have hvL : intervalDomainLift (v t) = intervalDomainLift (V t) := by
      rw [hEqV t ht.1 ht.2]
    rw [huL, hvL]
    exact hreg.2.2.2.1 t ht
  · -- Fifth conjunct: lifts of `u t, v t` equal lifts of `U t, V t`, so the
    -- closed-`Icc` `C²` + endpoint Neumann transfer verbatim.
    intro t ht
    have huL : intervalDomainLift (u t) = intervalDomainLift (U t) := by
      rw [hEq t ht.1 ht.2]
    have hvL : intervalDomainLift (v t) = intervalDomainLift (V t) := by
      rw [hEqV t ht.1 ht.2]
    rw [huL, hvL]
    exact hreg.2.2.2.2.1 t ht
  · -- Sixth conjunct: closed-slab joint `∂ₜ` continuity transfers via congr.
    obtain ⟨hjU, hjV⟩ := hreg.2.2.2.2.2.1
    have hliftEq : ∀ s, 0 < s → s < T →
        intervalDomainLift (u s) = intervalDomainLift (U s) := by
      intro s hs0 hsT; rw [hEq s hs0 hsT]
    have hliftEqV : ∀ s, 0 < s → s < T →
        intervalDomainLift (v s) = intervalDomainLift (V s) := by
      intro s hs0 hsT; rw [hEqV s hs0 hsT]
    refine ⟨ContinuousOn.congr hjU ?_, ContinuousOn.congr hjV ?_⟩
    · rintro ⟨t, x⟩ ⟨ht, _hx⟩
      simp only [Function.uncurry]
      have hEv : (fun s : ℝ => intervalDomainLift (u s) x) =ᶠ[nhds t]
          (fun s : ℝ => intervalDomainLift (U s) x) :=
        Set.EqOn.eventuallyEq_of_mem
          (fun s hs => by rw [hliftEq s hs.1 hs.2]) (isOpen_Ioo.mem_nhds ht)
      rw [hEv.deriv_eq]
    · rintro ⟨t, x⟩ ⟨ht, _hx⟩
      simp only [Function.uncurry]
      have hEv : (fun s : ℝ => intervalDomainLift (v s) x) =ᶠ[nhds t]
          (fun s : ℝ => intervalDomainLift (V s) x) :=
        Set.EqOn.eventuallyEq_of_mem
          (fun s hs => by rw [hliftEqV s hs.1 hs.2]) (isOpen_Ioo.mem_nhds ht)
      rw [hEv.deriv_eq]
  · -- Ninth conjunct (R1): closed-slab joint SOLUTION-field continuity transfers
    -- via congr.  On the slab `Ioo 0 T ×ˢ Icc 0 1` the field
    -- `(t,x) ↦ lift (u t) x` equals `(t,x) ↦ lift (U t) x` pointwise (since
    -- `u t = U t` for `t ∈ (0,T)`), so `ContinuousOn.congr` transfers `hreg`'s
    -- joint solution-field continuity.
    obtain ⟨hjU, hjV⟩ := hreg.2.2.2.2.2.2
    refine ⟨ContinuousOn.congr hjU ?_, ContinuousOn.congr hjV ?_⟩
    · rintro ⟨t, x⟩ ⟨ht, _hx⟩
      simp only [Function.uncurry]
      rw [hEq t ht.1 ht.2]
    · rintro ⟨t, x⟩ ⟨ht, _hx⟩
      simp only [Function.uncurry]
      rw [hEqV t ht.1 ht.2]

private lemma intervalDomainLift_eventuallyEq_of_pointwise_eq
    {f g : intervalDomainPoint → ℝ}
    (hfg : ∀ x : intervalDomainPoint, f x = g x)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    intervalDomainLift f =ᶠ[nhds x.1] intervalDomainLift g := by
  have hEqOn : Set.EqOn (intervalDomainLift f) (intervalDomainLift g)
      (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    unfold intervalDomainLift
    simp [hyIcc, hfg ⟨y, hyIcc⟩]
  exact Set.EqOn.eventuallyEq_of_mem hEqOn (isOpen_Ioo.mem_nhds hx)

private lemma intervalDomainLift_deriv_eventuallyEq_of_pointwise_eq
    {f g : intervalDomainPoint → ℝ}
    (hfg : ∀ x : intervalDomainPoint, f x = g x)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    (fun y => deriv (intervalDomainLift f) y) =ᶠ[nhds x.1]
      (fun y => deriv (intervalDomainLift g) y) := by
  have hEqOn : Set.EqOn
      (fun y => deriv (intervalDomainLift f) y)
      (fun y => deriv (intervalDomainLift g) y)
      (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hy_inside : (⟨y, hyIcc⟩ : intervalDomainPoint) ∈ intervalDomain.inside := hy
    exact Filter.EventuallyEq.deriv_eq
      (intervalDomainLift_eventuallyEq_of_pointwise_eq hfg hy_inside)
  exact Set.EqOn.eventuallyEq_of_mem hEqOn (isOpen_Ioo.mem_nhds hx)

private lemma intervalDomainTimeDeriv_eq_of_Ioo_eq
    {T t : ℝ} {u U : ℝ → intervalDomainPoint → ℝ}
    (hEq : ∀ s, 0 < s → s < T → u s = U s)
    (ht0 : 0 < t) (htT : t < T) (x : intervalDomainPoint) :
    intervalDomain.timeDeriv u t x = intervalDomain.timeDeriv U t x := by
  have hEqOn : Set.EqOn (fun s => u s x) (fun s => U s x) (Set.Ioo (0 : ℝ) T) := by
    intro s hs
    exact congrFun (hEq s hs.1 hs.2) x
  have heventually :
      (fun s => u s x) =ᶠ[nhds t] (fun s => U s x) :=
    Set.EqOn.eventuallyEq_of_mem hEqOn
      (isOpen_Ioo.mem_nhds ⟨ht0, htT⟩)
  change deriv (fun s : ℝ => u s x) t = deriv (fun s : ℝ => U s x) t
  exact Filter.EventuallyEq.deriv_eq heventually

private lemma intervalDomainLaplacian_eq_of_pointwise_eq
    {f g : intervalDomainPoint → ℝ}
    (hfg : ∀ x : intervalDomainPoint, f x = g x)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    intervalDomainLaplacian f x = intervalDomainLaplacian g x := by
  change deriv (fun y : ℝ => deriv (intervalDomainLift f) y) x.1 =
    deriv (fun y : ℝ => deriv (intervalDomainLift g) y) x.1
  exact Filter.EventuallyEq.deriv_eq
    (intervalDomainLift_deriv_eventuallyEq_of_pointwise_eq hfg hx)

private lemma intervalDomainChemotaxisDiv_eq_of_pointwise_eq
    (p : CM2Params)
    {u U v V : intervalDomainPoint → ℝ}
    (hu : ∀ x : intervalDomainPoint, u x = U x)
    (hv : ∀ x : intervalDomainPoint, v x = V x)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.inside) :
    intervalDomainChemotaxisDiv p u v x =
      intervalDomainChemotaxisDiv p U V x := by
  change deriv
      (fun y : ℝ =>
        intervalDomainLift u y * deriv (intervalDomainLift v) y /
          (1 + intervalDomainLift v y) ^ p.β) x.1 =
    deriv
      (fun y : ℝ =>
        intervalDomainLift U y * deriv (intervalDomainLift V) y /
          (1 + intervalDomainLift V y) ^ p.β) x.1
  have hEqOn : Set.EqOn
      (fun y : ℝ =>
        intervalDomainLift u y * deriv (intervalDomainLift v) y /
          (1 + intervalDomainLift v y) ^ p.β)
      (fun y : ℝ =>
        intervalDomainLift U y * deriv (intervalDomainLift V) y /
          (1 + intervalDomainLift V y) ^ p.β)
      (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hy_inside : (⟨y, hyIcc⟩ : intervalDomainPoint) ∈ intervalDomain.inside := hy
    have hlu :
        intervalDomainLift u y = intervalDomainLift U y := by
      have heq := intervalDomainLift_eventuallyEq_of_pointwise_eq hu hy_inside
      exact (Filter.EventuallyEq.eq_of_nhds heq)
    have hlv :
        intervalDomainLift v y = intervalDomainLift V y := by
      have heq := intervalDomainLift_eventuallyEq_of_pointwise_eq hv hy_inside
      exact (Filter.EventuallyEq.eq_of_nhds heq)
    have hdv :
        deriv (intervalDomainLift v) y = deriv (intervalDomainLift V) y :=
      Filter.EventuallyEq.deriv_eq
        (intervalDomainLift_eventuallyEq_of_pointwise_eq hv hy_inside)
    change intervalDomainLift u y * deriv (intervalDomainLift v) y /
        (1 + intervalDomainLift v y) ^ p.β =
      intervalDomainLift U y * deriv (intervalDomainLift V) y /
        (1 + intervalDomainLift V y) ^ p.β
    rw [hlu, hlv, hdv]
  exact Filter.EventuallyEq.deriv_eq
    (Set.EqOn.eventuallyEq_of_mem hEqOn (isOpen_Ioo.mem_nhds hx))

/-- The formal interval-domain classical-solution predicate is local under
pointwise agreement on `(0,T)`.  This closes the non-PDE locality layer of
the gluing argument. -/
theorem classicalSolutionLocalityUnderIooAgreement_intervalDomain
    (p : CM2Params) :
    ClassicalSolutionLocalityUnderIooAgreement p := by
  intro T u v U V hT hsol hEq
  have huEq : ∀ t, 0 < t → t < T → u t = U t := by
    intro t ht0 htT
    funext x
    exact (hEq t ht0 htT x).1
  have hvEq : ∀ t, 0 < t → t < T → v t = V t := by
    intro t ht0 htT
    funext x
    exact (hEq t ht0 htT x).2
  refine IsPaper2ClassicalSolution.of_components hT ?_ ?_ ?_ ?_ ?_ ?_
  · exact intervalDomainClassicalRegularity_congr_Ioo
      (u := u) (v := v) (U := U) (V := V) hsol.regularity huEq hvEq
  · intro t x ht0 htT
    rw [huEq t ht0 htT]
    exact hsol.u_pos' ht0 htT
  · intro t x ht0 htT
    rw [hvEq t ht0 htT]
    exact hsol.v_nonneg ht0 htT
  · intro t x ht0 htT hx
    have htime := intervalDomainTimeDeriv_eq_of_Ioo_eq huEq ht0 htT x
    have hlap :=
      intervalDomainLaplacian_eq_of_pointwise_eq
        (fun y => congrFun (huEq t ht0 htT) y) hx
    have hchem :=
      intervalDomainChemotaxisDiv_eq_of_pointwise_eq p
        (fun y => congrFun (huEq t ht0 htT) y)
        (fun y => congrFun (hvEq t ht0 htT) y) hx
    have hpde := hsol.pde_u ht0 htT hx
    have hlap' :
        intervalDomain.laplacian (u t) x = intervalDomain.laplacian (U t) x := by
      simpa [intervalDomain] using hlap
    have hchem' :
        intervalDomain.chemotaxisDiv p (u t) (v t) x =
          intervalDomain.chemotaxisDiv p (U t) (V t) x := by
      simpa [intervalDomain] using hchem
    have huval : u t x = U t x := congrFun (huEq t ht0 htT) x
    rw [htime, hlap', hchem', huval]
    exact hpde
  · intro t x ht0 htT hx
    have hlap :=
      intervalDomainLaplacian_eq_of_pointwise_eq
        (fun y => congrFun (hvEq t ht0 htT) y) hx
    have hpde := hsol.pde_v ht0 htT hx
    have hlap' :
        intervalDomain.laplacian (v t) x = intervalDomain.laplacian (V t) x := by
      simpa [intervalDomain] using hlap
    have huval : u t x = U t x := congrFun (huEq t ht0 htT) x
    have hvval : v t x = V t x := congrFun (hvEq t ht0 htT) x
    rw [hlap', hvval, huval]
    exact hpde
  · intro t x ht0 htT hx
    -- `u,v` agree with the base solution `U,V` as full functions on `(0,T)`, so the
    -- genuine Neumann conjunct transfers from `hsol`.
    rw [huEq t ht0 htT, hvEq t ht0 htT]
    exact hsol.neumann ht0 htT hx

/-- Canonical pointwise glued `u`: at each positive time `t`, choose the
finite reachable witness on horizon `t + 1`.  Nonpositive times are irrelevant
to the Paper 2 classical/global predicates and are filled with zero. -/
noncomputable def reachableArbitrarilyLongGluedU
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hreach : ReachableArbitrarilyLong p u₀) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if ht : 0 < t then
      (reachableClassicalSolutionDataOfReach
        (hreach (t + 1) (by linarith))).u t x
    else 0

/-- Canonical pointwise glued `v`, using the same horizon choice as
`reachableArbitrarilyLongGluedU`. -/
noncomputable def reachableArbitrarilyLongGluedV
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hreach : ReachableArbitrarilyLong p u₀) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if ht : 0 < t then
      (reachableClassicalSolutionDataOfReach
        (hreach (t + 1) (by linarith))).v t x
    else 0

/-- Under overlap uniqueness, the canonical glued branch agrees on `(0,T)`
with any chosen reachable witness on horizon `T`. -/
theorem reachableArbitrarilyLongGlued_eq_reachableData_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hreach : ReachableArbitrarilyLong p u₀)
    {T : ℝ} (d : ReachableClassicalSolutionData p u₀ T) :
    ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint,
      reachableArbitrarilyLongGluedU hreach t x = d.u t x ∧
      reachableArbitrarilyLongGluedV hreach t x = d.v t x := by
  intro t ht0 htT x
  let dshort : ReachableClassicalSolutionData p u₀ (t + 1) :=
    reachableClassicalSolutionDataOfReach (hreach (t + 1) (by linarith))
  have ht_overlap : t < min (t + 1) T := by
    exact lt_min (by linarith) htT
  have hsame := huniq dshort d t ht0 ht_overlap x
  constructor
  · simpa [reachableArbitrarilyLongGluedU, ht0, dshort] using hsame.1
  · simpa [reachableArbitrarilyLongGluedV, ht0, dshort] using hsame.2

/-- The glued branch inherits the initial trace from any reachable unit-horizon
witness, using overlap uniqueness for small positive times. -/
theorem reachableArbitrarilyLongGlued_initialTrace_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hreach : ReachableArbitrarilyLong p u₀) :
    InitialTrace intervalDomain u₀ (reachableArbitrarilyLongGluedU hreach) := by
  let d₁ : ReachableClassicalSolutionData p u₀ 1 :=
    reachableClassicalSolutionDataOfReach (hreach 1 one_pos)
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := d₁.trace ε hε
  refine ⟨min δ 1, lt_min hδ_pos one_pos, ?_⟩
  intro t ht0 ht_lt
  have htδ : t < δ := lt_of_lt_of_le ht_lt (min_le_left _ _)
  have ht1 : t < (1 : ℝ) := lt_of_lt_of_le ht_lt (min_le_right _ _)
  have hsame :=
    reachableArbitrarilyLongGlued_eq_reachableData_of_overlapUnique
      huniq hu₀ hreach d₁ t ht0 ht1
  have hfun :
      (fun x : intervalDomainPoint => reachableArbitrarilyLongGluedU hreach t x - u₀ x) =
        (fun x : intervalDomainPoint => d₁.u t x - u₀ x) := by
    funext x
    rw [(hsame x).1]
  change intervalDomainSupNorm
      (fun x : intervalDomainPoint => reachableArbitrarilyLongGluedU hreach t x - u₀ x) < ε
  rw [hfun]
  simpa [intervalDomain] using hδ_bound t ht0 htδ

/-- Gluing theorem with the exact remaining frontiers exposed.  Overlap
uniqueness gives pointwise compatibility of all finite witnesses; the locality
frontier upgrades that pointwise glued branch back into the formal classical
solution predicate on every finite horizon. -/
theorem GlobalSolutionGluingFromReachability_of_overlapUnique_and_locality
    {p : CM2Params}
    (huniq : IntervalClassicalSolutionOverlapUnique p)
    (hlocality : ClassicalSolutionLocalityUnderIooAgreement p) :
    GlobalSolutionGluingFromReachability p := by
  intro u₀ hu₀ hreach
  let u : ℝ → intervalDomainPoint → ℝ :=
    reachableArbitrarilyLongGluedU hreach
  let v : ℝ → intervalDomainPoint → ℝ :=
    reachableArbitrarilyLongGluedV hreach
  refine ⟨u, v, ?_, ?_⟩
  · intro T hT
    let dT : ReachableClassicalSolutionData p u₀ T :=
      reachableClassicalSolutionDataOfReach (hreach T hT)
    refine hlocality hT dT.sol ?_
    intro t ht0 htT x
    exact reachableArbitrarilyLongGlued_eq_reachableData_of_overlapUnique
      (huniq.at hu₀) hu₀ hreach dT t ht0 htT x
  · exact reachableArbitrarilyLongGlued_initialTrace_of_overlapUnique
      (huniq.at hu₀) hu₀ hreach

/-- Datum-specific canonical gluing.  Unlike the global frontier above, this
requires uniqueness only for the one datum whose reachable branches are being
glued. -/
theorem globalSolution_of_reachableArbitrarilyLong_of_overlapUniqueAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hreach : ReachableArbitrarilyLong p u₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
      InitialTrace intervalDomain u₀ u := by
  let u := reachableArbitrarilyLongGluedU hreach
  let v := reachableArbitrarilyLongGluedV hreach
  refine ⟨u, v, ?_, ?_⟩
  · intro T hT
    let dT : ReachableClassicalSolutionData p u₀ T :=
      reachableClassicalSolutionDataOfReach (hreach T hT)
    refine classicalSolutionLocalityUnderIooAgreement_intervalDomain p hT dT.sol ?_
    intro t ht0 htT x
    exact reachableArbitrarilyLongGlued_eq_reachableData_of_overlapUnique
      huniq hu₀ hreach dT t ht0 htT x
  · exact reachableArbitrarilyLongGlued_initialTrace_of_overlapUnique
      huniq hu₀ hreach

/-- The remaining gluing frontier is exactly overlap uniqueness.  The
calculus/locality layer for the concrete interval-domain classical predicate
is discharged by `classicalSolutionLocalityUnderIooAgreement_intervalDomain`. -/
theorem GlobalSolutionGluingFromReachability_of_overlapUnique
    {p : CM2Params}
    (huniq : IntervalClassicalSolutionOverlapUnique p) :
    GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_overlapUnique_and_locality
    huniq (classicalSolutionLocalityUnderIooAgreement_intervalDomain p)

/-- The sb-lyap energy-method uniqueness handoff supplies exactly the overlap
uniqueness input needed by the gluing construction. -/
theorem IntervalClassicalSolutionOverlapUnique_of_energyMethod
    {p : CM2Params}
    (hmethod : IntervalDomainClassicalUniquenessEnergyMethod p) :
    IntervalClassicalSolutionOverlapUnique p := by
  intro u₀ _hu₀ T₁ T₂ d₁ d₂ t ht0 ht_overlap x
  exact intervalDomain_classicalSolution_overlap_unique_of_energyMethod
    hmethod _hu₀ d₁.sol d₂.sol d₁.trace d₂.trace t ht0 ht_overlap x

/-- Arbitrarily long finite reachable solutions glue to a global solution once
the sb-lyap energy method supplies classical overlap uniqueness. -/
theorem GlobalSolutionGluingFromReachability_of_energyMethod
    {p : CM2Params}
    (hmethod : IntervalDomainClassicalUniquenessEnergyMethod p) :
    GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_overlapUnique
    (IntervalClassicalSolutionOverlapUnique_of_energyMethod hmethod)

/-- The concrete L2 uniqueness handoff supplies the overlap uniqueness input
needed by the gluing construction. -/
theorem IntervalClassicalSolutionOverlapUnique_of_l2EnergyMethod
    {p : CM2Params}
    (hmethod : IntervalDomainClassicalUniquenessL2EnergyMethod p) :
    IntervalClassicalSolutionOverlapUnique p := by
  intro u₀ hu₀ T₁ T₂ d₁ d₂ t ht0 ht_overlap x
  exact intervalDomain_classicalSolution_overlap_unique_of_l2EnergyMethod
    hmethod hu₀ d₁.sol d₂.sol d₁.trace d₂.trace t ht0 ht_overlap x

/-- Arbitrarily long finite reachable solutions glue to a global solution once
the L2 uniqueness handoff supplies equality on overlapping horizons. -/
theorem GlobalSolutionGluingFromReachability_of_l2EnergyMethod
    {p : CM2Params}
    (hmethod : IntervalDomainClassicalUniquenessL2EnergyMethod p) :
    GlobalSolutionGluingFromReachability p :=
  GlobalSolutionGluingFromReachability_of_overlapUnique
    (IntervalClassicalSolutionOverlapUnique_of_l2EnergyMethod hmethod)

/-!
Status of the uniqueness/gluing frontier:

* Closed here: arbitrary long finite reachable solutions glue to a global
  interval solution once overlap equality is available.  In particular, the
  L2 handoff `IntervalDomainClassicalUniquenessL2EnergyMethod p` gives
  `GlobalSolutionGluingFromReachability p`.
* Remaining upstream if one wants the theorem with no uniqueness parameter:
  construct `IntervalDomainClassicalUniquenessL2EnergyMethod p`, i.e. the
  concrete overlap L2 certificate for the coupled interval PDE.
-/

/-! #### Sup-realization from overlap uniqueness (structural sub-horizon gluing)

Goal: given `BddAbove (reachableClassicalHorizonSet p u₀)`, produce a classical
interval solution at horizon `T* = finiteMaximalReachableHorizon p u₀` with the
prescribed initial trace — i.e. discharge the `hrealize` umbrella hypothesis
internally, without any external PDE input beyond overlap uniqueness.

The construction is structural: for every `τ ∈ (0, T*)` there is a reachable
horizon `T_τ > τ` (because `τ < sSup` and the set is `BddAbove`-nonempty);
overlap uniqueness makes all the witnesses at different `T_τ` agree on the
common open interval `(0, T_τ)`, so they merge into one function on `(0, T*)`.
The merged function is then a classical solution AT horizon `T*` because the
nine-conjunct `intervalDomainClassicalRegularity` is local on the open slab
`Ioo 0 T* × Icc 0 1`, and on every sub-slab `Ioo 0 T_τ × Icc 0 1 ⊆ Ioo 0 T*
× Icc 0 1` the merged function coincides with a genuine classical witness.

This argument needs NO compactness/Ascoli-Arzelà input at the endpoint `T*`
(the predicate `IsPaper2ClassicalSolution intervalDomain p T* · ·` only
requires properties for `t ∈ (0, T*)` strictly). -/

/-- Pick a reachable horizon strictly above any `t < T*`.  Exists because
`t < sSup` and the reachable set is non-empty `BddAbove`. -/
private noncomputable def pickReachableAbove
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {t : ℝ} (ht : t < finiteMaximalReachableHorizon p u₀) :
    {T : ℝ // ReachableClassicalHorizon p u₀ T ∧ t < T} :=
  let h : ∃ T ∈ reachableClassicalHorizonSet p u₀, t < T :=
    (lt_csSup_iff hbdd hne).mp ht
  ⟨Classical.choose h,
    (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

/-- The packaged reachable witness chosen by `pickReachableAbove`. -/
private noncomputable def pickReachableAboveData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {t : ℝ} (ht : t < finiteMaximalReachableHorizon p u₀) :
    ReachableClassicalSolutionData p u₀
      (pickReachableAbove hbdd hne ht).1 :=
  reachableClassicalSolutionDataOfReach
    (pickReachableAbove hbdd hne ht).2.1

/-- The chosen reachable horizon strictly exceeds `t`. -/
private lemma pickReachableAbove_lt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {t : ℝ} (ht : t < finiteMaximalReachableHorizon p u₀) :
    t < (pickReachableAbove hbdd hne ht).1 :=
  (pickReachableAbove hbdd hne ht).2.2

/-- Glued `u` for the bounded reachable-horizon case: at every interior time
`t ∈ (0, T*)` use the witness on the chosen horizon `T_t > t`. -/
noncomputable def boundedReachableGluedU
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if h : 0 < t ∧ t < finiteMaximalReachableHorizon p u₀ then
      (pickReachableAboveData hbdd hne h.2).u t x
    else 0

/-- Glued `v` for the bounded reachable-horizon case, using the same chosen
witness as `boundedReachableGluedU`. -/
noncomputable def boundedReachableGluedV
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if h : 0 < t ∧ t < finiteMaximalReachableHorizon p u₀ then
      (pickReachableAboveData hbdd hne h.2).v t x
    else 0

/-- Under overlap uniqueness, the bounded-case glued branch agrees on
`(0, T)` with any chosen reachable witness on horizon `T ≤ T*`. -/
theorem boundedReachableGlued_eq_reachableData_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {T : ℝ} (d : ReachableClassicalSolutionData p u₀ T) :
    ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint,
      boundedReachableGluedU hbdd hne t x = d.u t x ∧
      boundedReachableGluedV hbdd hne t x = d.v t x := by
  intro t ht0 htT x
  -- The witness horizon `T` is ≤ T*.
  have hT_le : T ≤ finiteMaximalReachableHorizon p u₀ :=
    reachable_le_finiteMaximalReachableHorizon hbdd
      ⟨d.T_pos, d.u, d.v, d.sol, d.trace⟩
  have ht_lt_Tmax : t < finiteMaximalReachableHorizon p u₀ :=
    lt_of_lt_of_le htT hT_le
  -- Apply uniqueness between the chosen sub-horizon witness and `d`.
  let dpick : ReachableClassicalSolutionData p u₀
      (pickReachableAbove hbdd hne ht_lt_Tmax).1 :=
    pickReachableAboveData hbdd hne ht_lt_Tmax
  have ht_lt_pick : t < (pickReachableAbove hbdd hne ht_lt_Tmax).1 :=
    pickReachableAbove_lt hbdd hne ht_lt_Tmax
  have ht_overlap : t < min (pickReachableAbove hbdd hne ht_lt_Tmax).1 T :=
    lt_min ht_lt_pick htT
  have hsame := huniq dpick d t ht0 ht_overlap x
  refine ⟨?_, ?_⟩
  · -- `boundedReachableGluedU t x = dpick.u t x = d.u t x`.
    have h_if : boundedReachableGluedU hbdd hne t x = dpick.u t x := by
      unfold boundedReachableGluedU
      simp only [ht0, ht_lt_Tmax, and_self, dite_true, dpick,
        pickReachableAboveData]
    rw [h_if]; exact hsame.1
  · have h_if : boundedReachableGluedV hbdd hne t x = dpick.v t x := by
      unfold boundedReachableGluedV
      simp only [ht0, ht_lt_Tmax, and_self, dite_true, dpick,
        pickReachableAboveData]
    rw [h_if]; exact hsame.2

/-- Helper: for any `t ∈ (0, T*)` the glued branch matches its own chosen
witness pointwise at time `t`. -/
private lemma boundedReachableGlued_eq_pickWitness
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {t : ℝ} (ht0 : 0 < t) (ht_lt : t < finiteMaximalReachableHorizon p u₀) :
    ∀ x : intervalDomainPoint,
      boundedReachableGluedU hbdd hne t x =
          (pickReachableAboveData hbdd hne ht_lt).u t x ∧
        boundedReachableGluedV hbdd hne t x =
          (pickReachableAboveData hbdd hne ht_lt).v t x := by
  intro x
  refine ⟨?_, ?_⟩
  · unfold boundedReachableGluedU
    simp only [ht0, ht_lt, and_self, dite_true]
  · unfold boundedReachableGluedV
    simp only [ht0, ht_lt, and_self, dite_true]

/-- The glued branch on a sub-horizon `T < T*` agrees pointwise with the
chosen witness on the WHOLE open slab `Ioo 0 T`.  Same statement as
`boundedReachableGlued_eq_reachableData_of_overlapUnique` but packaged for
direct use by the `_congr_Ioo` regularity transfer. -/
private lemma boundedReachableGlued_eq_on_subSlab
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {T : ℝ} (d : ReachableClassicalSolutionData p u₀ T) :
    (∀ t, 0 < t → t < T → boundedReachableGluedU hbdd hne t = d.u t) ∧
      (∀ t, 0 < t → t < T → boundedReachableGluedV hbdd hne t = d.v t) := by
  refine ⟨?_, ?_⟩
  · intro t ht0 htT
    funext x
    exact (boundedReachableGlued_eq_reachableData_of_overlapUnique
      huniq hu₀ hbdd hne d t ht0 htT x).1
  · intro t ht0 htT
    funext x
    exact (boundedReachableGlued_eq_reachableData_of_overlapUnique
      huniq hu₀ hbdd hne d t ht0 htT x).2

/-- The glued branch inherits the initial trace from any chosen reachable
witness, using overlap uniqueness for small positive times.  Picks the witness
on the unique smallest reachable horizon via `hne`. -/
theorem boundedReachableGlued_initialTrace_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty) :
    InitialTrace intervalDomain u₀ (boundedReachableGluedU hbdd hne) := by
  -- Take ANY reachable witness from `hne` (kept named via choose).
  have hT₀mem : hne.choose ∈ reachableClassicalHorizonSet p u₀ := hne.choose_spec
  set T₀ : ℝ := hne.choose with hT₀def
  let d : ReachableClassicalSolutionData p u₀ T₀ :=
    reachableClassicalSolutionDataOfReach hT₀mem
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := d.trace ε hε
  refine ⟨min δ T₀, lt_min hδ_pos d.T_pos, ?_⟩
  intro t ht0 ht_lt
  have htδ : t < δ := lt_of_lt_of_le ht_lt (min_le_left _ _)
  have htT₀ : t < T₀ := lt_of_lt_of_le ht_lt (min_le_right _ _)
  have hsame :=
    boundedReachableGlued_eq_reachableData_of_overlapUnique
      huniq hu₀ hbdd hne d t ht0 htT₀
  have hfun :
      (fun x : intervalDomainPoint =>
          boundedReachableGluedU hbdd hne t x - u₀ x) =
        (fun x : intervalDomainPoint => d.u t x - u₀ x) := by
    funext x; rw [(hsame x).1]
  change intervalDomainSupNorm
      (fun x : intervalDomainPoint =>
        boundedReachableGluedU hbdd hne t x - u₀ x) < ε
  rw [hfun]
  simpa [intervalDomain] using hδ_bound t ht0 htδ

/-! ##### Conjunct-by-conjunct regularity transfer at horizon `T*`. -/

/-- The lifts of the glued `u` and the chosen witness `u` agree at every
interior time `t ∈ (0, T)`. -/
private lemma boundedReachableGluedU_lift_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {T : ℝ} (d : ReachableClassicalSolutionData p u₀ T) :
    ∀ t, 0 < t → t < T →
      intervalDomainLift (boundedReachableGluedU hbdd hne t) =
        intervalDomainLift (d.u t) := by
  intro t ht0 htT
  have hEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne d).1
    t ht0 htT
  rw [hEq]

private lemma boundedReachableGluedV_lift_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    {T : ℝ} (d : ReachableClassicalSolutionData p u₀ T) :
    ∀ t, 0 < t → t < T →
      intervalDomainLift (boundedReachableGluedV hbdd hne t) =
        intervalDomainLift (d.v t) := by
  intro t ht0 htT
  have hEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne d).2
    t ht0 htT
  rw [hEq]

/-- The classical regularity bundle holds for the glued branch at horizon
`T*`, obtained by locally restricting to a sub-horizon `T < T*` and applying
`intervalDomainClassicalRegularity_congr_Ioo` against the chosen witness
(plus joint-continuity local-to-global). -/
theorem boundedReachableGlued_classicalRegularity_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty) :
    intervalDomainClassicalRegularity
      (finiteMaximalReachableHorizon p u₀)
      (boundedReachableGluedU hbdd hne)
      (boundedReachableGluedV hbdd hne) := by
  set Tmax : ℝ := finiteMaximalReachableHorizon p u₀ with hTmaxDef
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (3) Spatial C² on Ioo 0 1 for u t, v t (per fixed interior t).
    intro t ht
    let dpick := pickReachableAboveData hbdd hne ht.2
    let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
    have huL := boundedReachableGluedU_lift_eq huniq hu₀ hbdd hne dpick t ht.1 hT_gt
    have hvL := boundedReachableGluedV_lift_eq huniq hu₀ hbdd hne dpick t ht.1 hT_gt
    rw [huL, hvL]
    exact dpick.sol.regularity.1 t ⟨ht.1, hT_gt⟩
  · -- (4) Per-point time differentiability + ∂ₜ continuity on Ioo 0 T*.
    intro x t ht
    let dpick := pickReachableAboveData hbdd hne ht.2
    let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
    have hreg4 := dpick.sol.regularity.2.1 x t ⟨ht.1, hT_gt⟩
    have hEqU := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).1
    have hEqV := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).2
    -- EventuallyEq for time slices.
    have huEv : (fun s : ℝ => boundedReachableGluedU hbdd hne s x) =ᶠ[nhds t]
        (fun s : ℝ => dpick.u s x) := by
      refine Set.EqOn.eventuallyEq_of_mem ?_
        (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick) ⟨ht.1, hT_gt⟩)
      intro s hs
      have := hEqU s hs.1 hs.2
      change boundedReachableGluedU hbdd hne s x = dpick.u s x
      rw [this]
    have hvEv : (fun s : ℝ => boundedReachableGluedV hbdd hne s x) =ᶠ[nhds t]
        (fun s : ℝ => dpick.v s x) := by
      refine Set.EqOn.eventuallyEq_of_mem ?_
        (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick) ⟨ht.1, hT_gt⟩)
      intro s hs
      have := hEqV s hs.1 hs.2
      change boundedReachableGluedV hbdd hne s x = dpick.v s x
      rw [this]
    refine ⟨⟨(huEv.differentiableAt_iff).mpr hreg4.1.1,
        (hvEv.differentiableAt_iff).mpr hreg4.1.2⟩, ?_, ?_⟩
    · -- ContinuousOn of `∂ₜ u·x` on Ioo 0 T*.
      apply continuousOn_of_locally_continuousOn
      intro t' ht'
      let dpick' := pickReachableAboveData hbdd hne ht'.2
      let Tpick' : ℝ := (pickReachableAbove hbdd hne ht'.2).1
      have hT_gt' : t' < Tpick' := pickReachableAbove_lt hbdd hne ht'.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick', isOpen_Ioo,
        ⟨ht'.1, hT_gt'⟩, ?_⟩
      have hreg4' := dpick'.sol.regularity.2.1 x
      -- Continuity of dpick'.u derivative on Ioo 0 Tpick' (any point gives same field).
      -- Use one chosen `t''` in Ioo to extract continuity.
      obtain ⟨t'', ht''⟩ : (Set.Ioo (0 : ℝ) Tpick').Nonempty :=
        ⟨Tpick' / 2, by constructor <;> linarith [dpick'.T_pos]⟩
      have hcontPick := (hreg4' t'' ht'').2.1
      have hsub : Set.Ioo (0 : ℝ) Tmax ∩ Set.Ioo (0 : ℝ) Tpick' ⊆
          Set.Ioo (0 : ℝ) Tpick' := Set.inter_subset_right
      have hcontPick' :
          ContinuousOn
            (fun s : ℝ => deriv (fun r : ℝ => dpick'.u r x) s)
            (Set.Ioo (0 : ℝ) Tmax ∩ Set.Ioo (0 : ℝ) Tpick') :=
        hcontPick.mono hsub
      apply hcontPick'.congr
      rintro s ⟨_, hs2⟩
      have hs0 : 0 < s := hs2.1
      have hsT : s < Tpick' := hs2.2
      have hsame :=
        (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick').1 s hs0 hsT
      have hEv : (fun r : ℝ => boundedReachableGluedU hbdd hne r x) =ᶠ[nhds s]
          (fun r : ℝ => dpick'.u r x) := by
        refine Set.EqOn.eventuallyEq_of_mem ?_
          (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick') hs2)
        intro r hr
        have := (boundedReachableGlued_eq_on_subSlab
          huniq hu₀ hbdd hne dpick').1 r hr.1 hr.2
        change boundedReachableGluedU hbdd hne r x = dpick'.u r x
        rw [this]
      simp only [hEv.deriv_eq]
    · -- ContinuousOn of `∂ₜ v·x` on Ioo 0 T*.
      apply continuousOn_of_locally_continuousOn
      intro t' ht'
      let dpick' := pickReachableAboveData hbdd hne ht'.2
      let Tpick' : ℝ := (pickReachableAbove hbdd hne ht'.2).1
      have hT_gt' : t' < Tpick' := pickReachableAbove_lt hbdd hne ht'.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick', isOpen_Ioo,
        ⟨ht'.1, hT_gt'⟩, ?_⟩
      have hreg4' := dpick'.sol.regularity.2.1 x
      obtain ⟨t'', ht''⟩ : (Set.Ioo (0 : ℝ) Tpick').Nonempty :=
        ⟨Tpick' / 2, by constructor <;> linarith [dpick'.T_pos]⟩
      have hcontPick := (hreg4' t'' ht'').2.2
      have hsub : Set.Ioo (0 : ℝ) Tmax ∩ Set.Ioo (0 : ℝ) Tpick' ⊆
          Set.Ioo (0 : ℝ) Tpick' := Set.inter_subset_right
      have hcontPick' :
          ContinuousOn
            (fun s : ℝ => deriv (fun r : ℝ => dpick'.v r x) s)
            (Set.Ioo (0 : ℝ) Tmax ∩ Set.Ioo (0 : ℝ) Tpick') :=
        hcontPick.mono hsub
      apply hcontPick'.congr
      rintro s ⟨_, hs2⟩
      have hs0 : 0 < s := hs2.1
      have hsT : s < Tpick' := hs2.2
      have hEv : (fun r : ℝ => boundedReachableGluedV hbdd hne r x) =ᶠ[nhds s]
          (fun r : ℝ => dpick'.v r x) := by
        refine Set.EqOn.eventuallyEq_of_mem ?_
          (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick') hs2)
        intro r hr
        have := (boundedReachableGlued_eq_on_subSlab
          huniq hu₀ hbdd hne dpick').2 r hr.1 hr.2
        change boundedReachableGluedV hbdd hne r x = dpick'.v r x
        rw [this]
      simp only [hEv.deriv_eq]
  · -- (5) Joint ∂ₜ continuity on `Ioo 0 T* × Ioo 0 1`.
    refine ⟨?_, ?_⟩
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      let dpick := pickReachableAboveData hbdd hne ht.2
      let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
      have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ,
        ⟨⟨ht.1, hT_gt⟩, Set.mem_univ _⟩, ?_⟩
      have hcontPick := dpick.sol.regularity.2.2.1.1
      -- hcontPick : ContinuousOn (uncurry ∂ₜ lift) (Ioo 0 Tpick × Ioo 0 1)
      have hsub :
          ((Set.Ioo (0 : ℝ) Tmax ×ˢ Set.Ioo (0 : ℝ) 1) ∩
            (Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ))
          ⊆ Set.Ioo (0 : ℝ) Tpick ×ˢ Set.Ioo (0 : ℝ) 1 := by
        rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
        exact ⟨hs2, hy1⟩
      have hcontPick' := hcontPick.mono hsub
      apply hcontPick'.congr
      rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
      simp only [Function.uncurry]
      have hLiftEq := boundedReachableGluedU_lift_eq
        huniq hu₀ hbdd hne dpick s hs2.1 hs2.2
      have hEv : (fun r : ℝ => intervalDomainLift
          (boundedReachableGluedU hbdd hne r) y) =ᶠ[nhds s]
            (fun r : ℝ => intervalDomainLift (dpick.u r) y) := by
        refine Set.EqOn.eventuallyEq_of_mem ?_
          (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick) hs2)
        intro r hr
        have hle := boundedReachableGluedU_lift_eq huniq hu₀ hbdd hne dpick
          r hr.1 hr.2
        change intervalDomainLift (boundedReachableGluedU hbdd hne r) y =
          intervalDomainLift (dpick.u r) y
        rw [hle]
      exact hEv.deriv_eq
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      let dpick := pickReachableAboveData hbdd hne ht.2
      let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
      have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ,
        ⟨⟨ht.1, hT_gt⟩, Set.mem_univ _⟩, ?_⟩
      have hcontPick := dpick.sol.regularity.2.2.1.2
      have hsub :
          ((Set.Ioo (0 : ℝ) Tmax ×ˢ Set.Ioo (0 : ℝ) 1) ∩
            (Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ))
          ⊆ Set.Ioo (0 : ℝ) Tpick ×ˢ Set.Ioo (0 : ℝ) 1 := by
        rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
        exact ⟨hs2, hy1⟩
      have hcontPick' := hcontPick.mono hsub
      apply hcontPick'.congr
      rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
      simp only [Function.uncurry]
      have hEv : (fun r : ℝ => intervalDomainLift
          (boundedReachableGluedV hbdd hne r) y) =ᶠ[nhds s]
            (fun r : ℝ => intervalDomainLift (dpick.v r) y) := by
        refine Set.EqOn.eventuallyEq_of_mem ?_
          (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick) hs2)
        intro r hr
        have hle := boundedReachableGluedV_lift_eq huniq hu₀ hbdd hne dpick
          r hr.1 hr.2
        change intervalDomainLift (boundedReachableGluedV hbdd hne r) y =
          intervalDomainLift (dpick.v r) y
        rw [hle]
      exact hEv.deriv_eq
  · -- (6) Endpoint tendsto for lift derivative (per fixed interior t).
    intro t ht
    let dpick := pickReachableAboveData hbdd hne ht.2
    let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
    have huL := boundedReachableGluedU_lift_eq huniq hu₀ hbdd hne dpick t ht.1 hT_gt
    have hvL := boundedReachableGluedV_lift_eq huniq hu₀ hbdd hne dpick t ht.1 hT_gt
    rw [huL, hvL]
    exact dpick.sol.regularity.2.2.2.1 t ⟨ht.1, hT_gt⟩
  · -- (7) Closed Icc C² + endpoint Neumann (per fixed interior t).
    intro t ht
    let dpick := pickReachableAboveData hbdd hne ht.2
    let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
    have huL := boundedReachableGluedU_lift_eq huniq hu₀ hbdd hne dpick t ht.1 hT_gt
    have hvL := boundedReachableGluedV_lift_eq huniq hu₀ hbdd hne dpick t ht.1 hT_gt
    rw [huL, hvL]
    exact dpick.sol.regularity.2.2.2.2.1 t ⟨ht.1, hT_gt⟩
  · -- (8) Closed-slab joint ∂ₜ continuity on `Ioo 0 T* × Icc 0 1`.
    refine ⟨?_, ?_⟩
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      let dpick := pickReachableAboveData hbdd hne ht.2
      let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
      have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ,
        ⟨⟨ht.1, hT_gt⟩, Set.mem_univ _⟩, ?_⟩
      have hcontPick := dpick.sol.regularity.2.2.2.2.2.1.1
      have hsub :
          ((Set.Ioo (0 : ℝ) Tmax ×ˢ Set.Icc (0 : ℝ) 1) ∩
            (Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ))
          ⊆ Set.Ioo (0 : ℝ) Tpick ×ˢ Set.Icc (0 : ℝ) 1 := by
        rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
        exact ⟨hs2, hy1⟩
      have hcontPick' := hcontPick.mono hsub
      apply hcontPick'.congr
      rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
      simp only [Function.uncurry]
      have hEv : (fun r : ℝ => intervalDomainLift
          (boundedReachableGluedU hbdd hne r) y) =ᶠ[nhds s]
            (fun r : ℝ => intervalDomainLift (dpick.u r) y) := by
        refine Set.EqOn.eventuallyEq_of_mem ?_
          (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick) hs2)
        intro r hr
        have hle := boundedReachableGluedU_lift_eq huniq hu₀ hbdd hne dpick
          r hr.1 hr.2
        change intervalDomainLift (boundedReachableGluedU hbdd hne r) y =
          intervalDomainLift (dpick.u r) y
        rw [hle]
      exact hEv.deriv_eq
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      let dpick := pickReachableAboveData hbdd hne ht.2
      let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
      have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ,
        ⟨⟨ht.1, hT_gt⟩, Set.mem_univ _⟩, ?_⟩
      have hcontPick := dpick.sol.regularity.2.2.2.2.2.1.2
      have hsub :
          ((Set.Ioo (0 : ℝ) Tmax ×ˢ Set.Icc (0 : ℝ) 1) ∩
            (Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ))
          ⊆ Set.Ioo (0 : ℝ) Tpick ×ˢ Set.Icc (0 : ℝ) 1 := by
        rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
        exact ⟨hs2, hy1⟩
      have hcontPick' := hcontPick.mono hsub
      apply hcontPick'.congr
      rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
      simp only [Function.uncurry]
      have hEv : (fun r : ℝ => intervalDomainLift
          (boundedReachableGluedV hbdd hne r) y) =ᶠ[nhds s]
            (fun r : ℝ => intervalDomainLift (dpick.v r) y) := by
        refine Set.EqOn.eventuallyEq_of_mem ?_
          (isOpen_Ioo.mem_nhds (s := Set.Ioo (0 : ℝ) Tpick) hs2)
        intro r hr
        have hle := boundedReachableGluedV_lift_eq huniq hu₀ hbdd hne dpick
          r hr.1 hr.2
        change intervalDomainLift (boundedReachableGluedV hbdd hne r) y =
          intervalDomainLift (dpick.v r) y
        rw [hle]
      exact hEv.deriv_eq
  · -- (9) Closed-slab joint SOLUTION-FIELD continuity on `Ioo 0 T* × Icc 0 1`.
    refine ⟨?_, ?_⟩
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      let dpick := pickReachableAboveData hbdd hne ht.2
      let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
      have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ,
        ⟨⟨ht.1, hT_gt⟩, Set.mem_univ _⟩, ?_⟩
      have hcontPick := dpick.sol.regularity.2.2.2.2.2.2.1
      have hsub :
          ((Set.Ioo (0 : ℝ) Tmax ×ˢ Set.Icc (0 : ℝ) 1) ∩
            (Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ))
          ⊆ Set.Ioo (0 : ℝ) Tpick ×ˢ Set.Icc (0 : ℝ) 1 := by
        rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
        exact ⟨hs2, hy1⟩
      have hcontPick' := hcontPick.mono hsub
      apply hcontPick'.congr
      rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
      simp only [Function.uncurry]
      have hle := boundedReachableGluedU_lift_eq huniq hu₀ hbdd hne dpick
        s hs2.1 hs2.2
      change intervalDomainLift (boundedReachableGluedU hbdd hne s) y =
        intervalDomainLift (dpick.u s) y
      rw [hle]
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      let dpick := pickReachableAboveData hbdd hne ht.2
      let Tpick : ℝ := (pickReachableAbove hbdd hne ht.2).1
      have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne ht.2
      refine ⟨Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ,
        ⟨⟨ht.1, hT_gt⟩, Set.mem_univ _⟩, ?_⟩
      have hcontPick := dpick.sol.regularity.2.2.2.2.2.2.2
      have hsub :
          ((Set.Ioo (0 : ℝ) Tmax ×ˢ Set.Icc (0 : ℝ) 1) ∩
            (Set.Ioo (0 : ℝ) Tpick ×ˢ Set.univ))
          ⊆ Set.Ioo (0 : ℝ) Tpick ×ˢ Set.Icc (0 : ℝ) 1 := by
        rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
        exact ⟨hs2, hy1⟩
      have hcontPick' := hcontPick.mono hsub
      apply hcontPick'.congr
      rintro ⟨s, y⟩ ⟨⟨hs1, hy1⟩, hs2, _⟩
      simp only [Function.uncurry]
      have hle := boundedReachableGluedV_lift_eq huniq hu₀ hbdd hne dpick
        s hs2.1 hs2.2
      change intervalDomainLift (boundedReachableGluedV hbdd hne s) y =
        intervalDomainLift (dpick.v s) y
      rw [hle]

/-- The glued branch is a classical interval solution at horizon `T*`. -/
theorem boundedReachableGlued_isPaper2ClassicalSolution_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUniqueAt p u₀)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
    (hne : (reachableClassicalHorizonSet p u₀).Nonempty)
    (hTmax_pos : 0 < finiteMaximalReachableHorizon p u₀) :
    IsPaper2ClassicalSolution intervalDomain p
      (finiteMaximalReachableHorizon p u₀)
      (boundedReachableGluedU hbdd hne)
      (boundedReachableGluedV hbdd hne) := by
  set Tmax : ℝ := finiteMaximalReachableHorizon p u₀ with hTmaxDef
  refine IsPaper2ClassicalSolution.of_components hTmax_pos
    (boundedReachableGlued_classicalRegularity_of_overlapUnique
      huniq hu₀ hbdd hne)
    ?hpos ?hv_nonneg ?hpde_u ?hpde_v ?hneumann
  case hpos =>
    intro t x ht0 htT
    let dpick := pickReachableAboveData hbdd hne htT
    let Tpick : ℝ := (pickReachableAbove hbdd hne htT).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne htT
    have heq :=
      (boundedReachableGlued_eq_reachableData_of_overlapUnique
        huniq hu₀ hbdd hne dpick t ht0 hT_gt x).1
    rw [heq]
    exact dpick.sol.u_pos' ht0 hT_gt
  case hv_nonneg =>
    intro t x ht0 htT
    let dpick := pickReachableAboveData hbdd hne htT
    let Tpick : ℝ := (pickReachableAbove hbdd hne htT).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne htT
    have heq :=
      (boundedReachableGlued_eq_reachableData_of_overlapUnique
        huniq hu₀ hbdd hne dpick t ht0 hT_gt x).2
    rw [heq]
    exact dpick.sol.v_nonneg ht0 hT_gt
  case hpde_u =>
    intro t x ht0 htT hx
    let dpick := pickReachableAboveData hbdd hne htT
    let Tpick : ℝ := (pickReachableAbove hbdd hne htT).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne htT
    have huEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).1
    have hvEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).2
    have htime :=
      intervalDomainTimeDeriv_eq_of_Ioo_eq (T := Tpick) huEq ht0 hT_gt x
    have hlap :=
      intervalDomainLaplacian_eq_of_pointwise_eq
        (fun y => congrFun (huEq t ht0 hT_gt) y) hx
    have hchem :=
      intervalDomainChemotaxisDiv_eq_of_pointwise_eq p
        (fun y => congrFun (huEq t ht0 hT_gt) y)
        (fun y => congrFun (hvEq t ht0 hT_gt) y) hx
    have hpde := dpick.sol.pde_u ht0 hT_gt hx
    have hlap' :
        intervalDomain.laplacian (boundedReachableGluedU hbdd hne t) x =
          intervalDomain.laplacian (dpick.u t) x := by
      simpa [intervalDomain] using hlap
    have hchem' :
        intervalDomain.chemotaxisDiv p
            (boundedReachableGluedU hbdd hne t)
            (boundedReachableGluedV hbdd hne t) x =
          intervalDomain.chemotaxisDiv p (dpick.u t) (dpick.v t) x := by
      simpa [intervalDomain] using hchem
    have huval : boundedReachableGluedU hbdd hne t x = dpick.u t x :=
      congrFun (huEq t ht0 hT_gt) x
    rw [htime, hlap', hchem', huval]
    exact hpde
  case hpde_v =>
    intro t x ht0 htT hx
    let dpick := pickReachableAboveData hbdd hne htT
    let Tpick : ℝ := (pickReachableAbove hbdd hne htT).1
    have hT_gt : t < Tpick := pickReachableAbove_lt hbdd hne htT
    have huEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).1
    have hvEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).2
    have hlap :=
      intervalDomainLaplacian_eq_of_pointwise_eq
        (fun y => congrFun (hvEq t ht0 hT_gt) y) hx
    have hpde := dpick.sol.pde_v ht0 hT_gt hx
    have hlap' :
        intervalDomain.laplacian (boundedReachableGluedV hbdd hne t) x =
          intervalDomain.laplacian (dpick.v t) x := by
      simpa [intervalDomain] using hlap
    have huval : boundedReachableGluedU hbdd hne t x = dpick.u t x :=
      congrFun (huEq t ht0 hT_gt) x
    have hvval : boundedReachableGluedV hbdd hne t x = dpick.v t x :=
      congrFun (hvEq t ht0 hT_gt) x
    rw [hlap', hvval, huval]
    exact hpde
  case hneumann =>
    intro t x ht0 htT hx
    let dpick := pickReachableAboveData hbdd hne htT
    have hT_gt : t < (pickReachableAbove hbdd hne htT).1 :=
      pickReachableAbove_lt hbdd hne htT
    have huEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).1
    have hvEq := (boundedReachableGlued_eq_on_subSlab huniq hu₀ hbdd hne dpick).2
    -- The glued solution agrees with the picked finite-horizon solution as full
    -- functions on the sub-slab, so the genuine Neumann conjunct transfers.
    rw [huEq t ht0 hT_gt, hvEq t ht0 hT_gt]
    exact dpick.sol.neumann ht0 hT_gt hx

/-- Bundle: under overlap uniqueness, the `hrealize` umbrella hypothesis is
discharged internally — a classical interval solution at horizon `T*` with the
prescribed initial trace exists. -/
theorem realize_at_finiteMaximalReachableHorizon_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalClassicalSolutionOverlapUnique p)
    (hlocal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2ClassicalSolution intervalDomain p T u v ∧
            InitialTrace intervalDomain u₀ u)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSet p u₀)) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p
        (finiteMaximalReachableHorizon p u₀) u v ∧
      InitialTrace intervalDomain u₀ u := by
  have hne : (reachableClassicalHorizonSet p u₀).Nonempty :=
    reachableClassicalHorizonSet_nonempty_of_localExistence p hlocal hu₀
  have hTmax_pos : 0 < finiteMaximalReachableHorizon p u₀ :=
    finiteMaximalReachableHorizon_pos_of_localExistence p hlocal hu₀ hbdd
  refine ⟨boundedReachableGluedU hbdd hne, boundedReachableGluedV hbdd hne,
    boundedReachableGlued_isPaper2ClassicalSolution_of_overlapUnique
      (huniq.at hu₀) hu₀ hbdd hne hTmax_pos,
    boundedReachableGlued_initialTrace_of_overlapUnique (huniq.at hu₀) hu₀ hbdd hne⟩

/-! #### Blow-up exclusion from an a priori bound

The standard continuation theorem produces a finite branch only if the
`m ≥ 1` blow-up alternative can occur.  The lemmas in this block isolate the
exact formal input needed to turn the Theorem 1.2-style a priori bound into
the negation of that branch.  Because the concrete `intervalDomainSupNorm` is
defined as `sSup (range |f|)`, pointwise control from a sup-norm bound also
requires the usual spatial boundedness of each time slice; this is not encoded
in the current `intervalDomainClassicalRegularity` field. -/

/-- A finite-horizon solution is pointwise bounded from above before `T`. -/
def PointwiseBoundedBefore
    (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∃ M, ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside → u t x ≤ M

/-- On a finite horizon, the concrete sup norm controls point values of the
solution.  For the current interval-domain formal interface this is a separate
spatial-regularity input: `intervalDomainClassicalRegularity` only controls the
time trace of the sup norm, not spatial continuity/boundedness of `u t`. -/
def SupNormControlsPointwiseBefore
    (T : ℝ) (u : ℝ → intervalDomain.Point → ℝ) : Prop :=
  ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
    u t x ≤ intervalDomain.supNorm (u t)

/-- If every relevant time slice has bounded `range |u t|`, then the concrete
`intervalDomain.supNorm` controls point values on the open interval. -/
theorem supNormControlsPointwiseBefore_of_bddAbove_abs
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hbdd :
      ∀ t, 0 < t → t < T →
        BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|))) :
    SupNormControlsPointwiseBefore T u := by
  intro t x ht0 htT _hx
  have habs_le :
      |u t x| ≤ intervalDomain.supNorm (u t) := by
    change |u t x| ≤ intervalDomainSupNorm (u t)
    unfold intervalDomainSupNorm
    exact le_csSup (hbdd t ht0 htT) ⟨x, rfl⟩
  exact le_trans (le_abs_self (u t x)) habs_le

/-- A finite-horizon sup-norm bound becomes a pointwise upper bound once the
sup norm is known to control point values. -/
theorem pointwiseBoundedBefore_of_boundedBefore_and_supNormControls
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (hcontrols : SupNormControlsPointwiseBefore T u) :
    PointwiseBoundedBefore T u := by
  rcases hbounded with ⟨M, hM⟩
  exact ⟨M, fun t x ht0 htT hx =>
    le_trans (hcontrols t x ht0 htT hx) (hM t ht0 htT)⟩

/-- A pointwise upper bound rules out the `m ≥ 1` finite-time blow-up
alternative. -/
theorem not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore
    {T : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hbounded : PointwiseBoundedBefore T u) :
    ¬ MGeOneFiniteHorizonAlternative intervalDomain T u := by
  intro hblow
  rcases hbounded with ⟨M, hM⟩
  rcases hblow M with ⟨t, x, ht0, htT, hx, hlt⟩
  exact not_lt_of_ge (hM t x ht0 htT hx) hlt

/-- The Theorem 1.2-style a priori finite-horizon bound, together with the
spatial fact that `supNorm` controls point values, rules out the finite branch
of the maximal-continuation alternative when `1 ≤ m`. -/
theorem not_finiteContinuationAlternativeBranch_of_boundedBefore_and_supNormControl
    {p : CM2Params} {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hm : 1 ≤ p.m)
    (hboundedBefore :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain T u)
    (hsupControls :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          SupNormControlsPointwiseBefore T u) :
    ¬ FiniteContinuationAlternativeBranch p u₀ := by
  intro hfinite
  rcases hfinite with ⟨T, hT, u, v, hsol, htrace, _halt, hmge⟩
  have hpw :
      PointwiseBoundedBefore T u :=
    pointwiseBoundedBefore_of_boundedBefore_and_supNormControls
      (hboundedBefore u₀ hu₀ T hT u v hsol htrace)
      (hsupControls u₀ hu₀ T hT u v hsol htrace)
  exact not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore hpw
    (hmge hm)

/-- If the standard continuation alternative holds, the finite branch is ruled
out for `1 ≤ m`, and arbitrarily long reachable horizons can be glued, then the
corrected existential-global package follows. -/
theorem intervalDomainGlobalSolutionExists_of_standardContinuation_and_gluing
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hstandard :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          1 ≤ p.m → StandardContinuationAlternative p u₀)
    (hnoFinite :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          1 ≤ p.m → ¬ FiniteContinuationAlternativeBranch p u₀)
    (hglue : GlobalSolutionGluingFromReachability p) :
    IntervalDomainGlobalSolutionExists p := by
  refine intervalDomainGlobalSolutionExists_of_local_global_bounded_initial
    p hlocal hboundedInitial ?_
  intro u₀ hu₀ hm
  rcases hstandard u₀ hu₀ hm with hlong | hfinite
  · exact hglue u₀ hu₀ hlong
  · exact False.elim ((hnoFinite u₀ hu₀ hm) hfinite)

/-- Bridge from the finite-sup maximal-continuation skeleton already proved in
this file to the corrected existential-global package.  The hypotheses are the
remaining PDE continuation/gluing frontiers, stated directly rather than hidden
inside the old false same-tail field. -/
theorem intervalDomainGlobalSolutionExists_of_finiteSup_continuation_and_gluing
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove (reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀))
    (hnoFinite :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          1 ≤ p.m → ¬ FiniteContinuationAlternativeBranch p u₀)
    (hglue : GlobalSolutionGluingFromReachability p) :
    IntervalDomainGlobalSolutionExists p := by
  refine intervalDomainGlobalSolutionExists_of_standardContinuation_and_gluing
    p hlocal hboundedInitial ?_ hnoFinite hglue
  intro u₀ hu₀ _hm
  exact standardContinuationAlternative_of_finiteSup_realization_and_extension
    p hlocal hu₀
    (hrealize u₀ hu₀)
    (hextend_of_not_finiteAlternative u₀ hu₀)
    (hextend_of_not_mgeAlternative u₀ hu₀)

/-- Maximal continuation plus an a priori finite-horizon bound gives the
corrected existential-global package.

This is the bridge needed after the Theorem 1.2-style boundedness theorem:
`hboundedBefore` is the finite-horizon sup-norm bound for every classical
branch, `hsupControls` is the spatial regularity fact converting that concrete
sup norm into pointwise control, and `hglue` is the uniqueness/gluing theorem
turning arbitrarily long compatible finite horizons into one global solution.
The old false same-tail `globalExtension` field is not used. -/
theorem intervalDomainGlobalSolutionExists_of_boundedContinuation_and_gluing
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove (reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀))
    (hboundedBefore :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain T u)
    (hsupControls :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          SupNormControlsPointwiseBefore T u)
    (hglue : GlobalSolutionGluingFromReachability p) :
    IntervalDomainGlobalSolutionExists p := by
  refine intervalDomainGlobalSolutionExists_of_finiteSup_continuation_and_gluing
    p hlocal hboundedInitial hrealize
    hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative ?_ hglue
  intro u₀ hu₀ hm
  exact
    not_finiteContinuationAlternativeBranch_of_boundedBefore_and_supNormControl
      hu₀ hm hboundedBefore hsupControls

/-- Variant of the previous bridge where the spatial `supNorm` control is
obtained from boundedness of the absolute-value range of every time slice. -/
theorem intervalDomainGlobalSolutionExists_of_boundedContinuation_rangeBounded_and_gluing
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove (reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove (reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (finiteMaximalReachableHorizon p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (finiteMaximalReachableHorizon p u₀) u →
          ReachablePast p u₀ (finiteMaximalReachableHorizon p u₀))
    (hboundedBefore :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain T u)
    (hrangeBounded :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ t, 0 < t → t < T →
            BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)))
    (hglue : GlobalSolutionGluingFromReachability p) :
    IntervalDomainGlobalSolutionExists p := by
  refine
    intervalDomainGlobalSolutionExists_of_boundedContinuation_and_gluing
      p hlocal hboundedInitial hrealize
      hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative
      hboundedBefore ?_ hglue
  intro u₀ hu₀ T hT u v hsol htrace
  exact supNormControlsPointwiseBefore_of_bddAbove_abs
    (hrangeBounded u₀ hu₀ T hT u v hsol htrace)

/-- Concrete Picard/Duhamel local existence plus the corrected existential
global-continuation theorem gives the corrected package. -/
theorem intervalDomainGlobalSolutionExists_of_intervalDuhamel_contraction_regularization
    (p : CM2Params)
    (hmild :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ L > 0, ∃ D₀ ≥ 0, ∃ T > 0,
            L * T < 1 ∧
            (∀ (u₁ u₂ : ℝ → intervalDomainPoint → ℝ) (D : ℝ),
              0 ≤ D →
              (∀ s y, 0 ≤ s → s ≤ T →
                |u₁ s y - u₂ s y| ≤ D) →
              ∀ t x, 0 ≤ t → t ≤ T →
                |intervalDuhamelOperator p u₀ u₁ t x -
                  intervalDuhamelOperator p u₀ u₂ t x| ≤ L * T * D) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              |intervalDuhamelOperator p u₀ (fun _ _ => 0) t x| ≤ D₀) ∧
            (∀ u : ℝ → intervalDomainPoint → ℝ,
              (∀ t x, 0 ≤ t → t ≤ T →
                u t x = intervalDuhamelOperator p u₀ u t x) →
                RegularityBootstrap p T u₀ u))
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          1 ≤ p.m → IntervalDomainGlobalSolutionFor p u₀) :
    IntervalDomainGlobalSolutionExists p := by
  exact intervalDomainGlobalSolutionExists_of_local_global_bounded_initial p
    (intervalDomain_localExistence_of_intervalDuhamel_contraction_regularization
      p hmild)
    hboundedInitial hglobal

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

/-! ### Honest status of localExistence on intervalDomain

The full `IntervalDomainExistence.localExistence` requires `∀ u₀, PID u₀ →
∃ Tmax u v, IsPaper2ClassicalSolution ∧ InitialTrace`.

**What IS proved** (constant-in-space initial data):
- `constantSolution_localExistence_with_trace`: (a>0,b>0) or (a=0,b=0)
- `aboveEquilibrium_localExistence`: a>0, b>0, c₀ ≥ (a/b)^{1/α}

**What IS proved** (abstract chain):
- `localExistence_from_banach_and_regularity`: reduces to RegularityBootstrap
- `localExistence_conditional`: reduces to IsMildSolutionData
- Banach FP (`duhamel_mild_solution_exists`) + contraction estimates
- B2 interval-Duhamel wiring:
  `intervalDuhamel_fixed_point_exists_of_contraction` constructs the concrete
  mild fixed point from the Picard/Banach contraction;
  `localExistence_of_intervalDuhamel_contraction_and_regularization` turns it
  into local classical existence once concrete Duhamel regularization is proved;
  `intervalDomain_localExistence_of_intervalDuhamel_contraction_regularization`
  closes the full local-existence field for every positive initial datum under
  those same concrete Picard/Duhamel hypotheses;
  `intervalDuhamel_fixed_point_unique_of_contraction` gives uniqueness for
  bounded local fixed points in the contraction ball;
  `reachableClassicalHorizon_mono` proves that reachable classical horizons are
  downward closed;
  `reachableArbitrarilyLong_of_not_bddAbove` proves the global branch when the
  reachable-horizon set is unbounded;
  `standardContinuationAlternative_of_finiteSup_realization_and_extension`
  proves the standard maximal-continuation dichotomy from finite-sup
  realization plus endpoint continuation past any failed alternative;
  `equilibrium_reachableClassicalHorizonSet_not_bddAbove` formally records
  that positive equilibrium data lies in the unbounded/global branch;
  `Proposition_1_1_intervalDomain_of_localExistence_and_finiteHorizonAlternative`
  isolates the exact remaining proposition-level frontier;
  `Proposition_1_1_intervalDomain_of_intervalDuhamel_contraction_regularization`
  closes `Proposition_1_1 intervalDomain p` conditional on the same concrete
  regularization plus the genuine maximal-continuation/blow-up alternative.

**What is BLOCKED**:
1. Below-equilibrium constant data (0 < c < (a/b)^{1/α}):
   `intervalDomainClassicalRegularity` quantifies `∀ p : CM2Params`,
   requiring sup-norm nonincreasing for ALL parameter sets, not just the
   given p. An increasing ODE solution violates this for small thresholds.
   This is a design issue in IntervalDomain.lean (the paper's Lemma 3.1
   only uses the GIVEN p), not a mathematical limitation.

2. Non-constant initial data:
   Requires RegularityBootstrap for the Duhamel fixed point, which needs
   parabolic regularity theory (mild → classical) + comparison principle
   (positivity) + strong maximum principle (sup norm control).

3. The order-theoretic part of maximal continuation is proved, but the analytic
   finite-sup branch still needs:
   (a) realization of the finite `sSup` by a classical solution on `(0,Tmax)`,
   via compactness/gluing of reachable-horizon solutions;
   (b) endpoint trace/compactness strong enough to restart local existence at
   times approaching `Tmax`;
   (c) uniqueness strong enough to paste the restarted solution to the
   pre-existing branch.  The scalar `ODEUniqueness.lean` lemmas handle only
   Bernoulli/logistic profiles; the file does not yet contain PDE uniqueness
   for arbitrary interval classical solutions.

4. The current formal `Proposition_1_1 intervalDomain p` has only a finite
   `Tmax` branch.  The standard maximal-continuation theorem has a global
   alternative, and the positive equilibrium theorem proves this global branch
   is not vacuous.  Therefore the current proposition cannot be obtained from
   standard continuation without either adding a global branch to the statement
   or proving an additional hypothesis that excludes global solutions, which is
   false for positive equilibrium data.

5. The current concrete `intervalDuhamelOperator` contains the logistic source
   transported by the Neumann heat semigroup.  The full
   `IsPaper2ClassicalSolution` still contains the chemotaxis term and elliptic
   signal equation, so `RegularityBootstrap` must come from a concrete
   Duhamel/Picard regularization theorem that also supplies positivity,
   the elliptic `v`, Neumann traces, and the stated `classicalRegularity`.

**The gap is precisely identified**: prove RegularityBootstrap for the concrete
Duhamel FP and prove the maximal-continuation/blow-up alternative; do not use the
invalid arbitrary-domain regularity shortcut. -/

/-! ### Design issue: `classicalRegularity` blocks below-equilibrium

The full `localExistence` (∀ u₀) is expected to be FALSE for some
CM2Params on intervalDomain, due to the `∀ p` quantification in
`intervalDomainClassicalRegularity`.

**Informal argument**: For p with a=1, b=1, α=1 and u₀ = 1/2 < 1 = (a/b)^{1/α},
any classical solution has u increasing (since u(a-bu^α) > 0 when u < 1).
For p' with b'=10^6: threshold = 10^{-6} < 1/2, so `classicalRegularity`
requires supNorm nonincreasing — contradicting the increase.

**Formal refutation not proved** because deriving the contradiction requires
showing that the supNorm of ANY classical solution with this initial datum
must increase, which needs the full PDE maximum principle argument.

**This is a design issue**: the paper's Lemma 3.1 uses the GIVEN p only.
The `∀ p` quantification in `intervalDomainClassicalRegularity` is over-strong.
Fix: parameterize `classicalRegularity` by `p` instead of quantifying over all. -/

end ShenWork.IntervalDomainExistence

end
