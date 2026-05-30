/-
  ShenWork/Paper2/IntervalDomainL2PDEIntegral.lean

  **T5 tail R2 — the PDE-substitution frontier `hPDEIntegral`, reduced to
  integrability.**

  `hPDEIntegral` is the spatial integral of the pointwise parabolic identity:

    `∫₀¹ u·∂ₜu = ∫₀¹ u·Δu − χ₀ ∫₀¹ u·chemDiv + ∫₀¹ u²(a − b u^α)`.

  The pointwise identity `u·∂ₜu = u·(Δu − χ₀·chemDiv + u(a−bu^α))` is already proved
  (`intervalDomain_solution_l2_weighted_timeDeriv_eq_pde`, on the interior).  This
  file discharges the *integration* of that identity:

  * lift linearity + the interior pointwise PDE give, a.e. on `[0,1]`, the lifted
    integrand equality;
  * `intervalIntegral.integral_{add,sub,const_mul}` split the integral into the
    three named pieces — *provided* each lifted piece is interval-integrable.

  `intervalDomain_l2_half_energy_hPDEIntegral_of_integrable` therefore reduces
  `hPDEIntegral` to exactly THREE integrability facts:

  * `hA` — `∫₀¹ u·Δu`: provable from conjunct (7) closed-`C²` (`u` and `Δu`
    continuous on `[0,1]`).  Discharged here as
    `intervalDomainLift_diffusion_intervalIntegrable_of_regularity`.
  * `hC` — `∫₀¹ u²(a−bu^α)`: continuous in `u`, but the `u^α` real power needs
    `u ≥ 0` (solution positivity) for continuity — left as an honest input.
  * `hB` — `∫₀¹ u·chemDiv`: the chemotaxis flux divergence, coupling to `v`’s
    `C²` regularity and `1+v` bounded below — the genuine `v`-coupled frontier.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainProfileIBP
import ShenWork.PDE.IntervalProfileBoundaryRegularity

open ShenWork.IntervalDomain MeasureTheory
open scoped Topology

namespace ShenWork.Paper2

noncomputable section

open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalFullKernelRegularity

/-- **The PDE-substitution identity `hPDEIntegral`, reduced to integrability.**
Given interval-integrability of the three lifted integrands — the diffusion term
`u·Δu` (`hA`), the chemotaxis term `u·chemDiv` (`hB`), and the logistic term
`u²(a−bu^α)` (`hC`) — the spatial integral of `u·∂ₜu` splits into the three named
energy integrals.  The pointwise parabolic identity is supplied on the interior by
`intervalDomain_solution_l2_weighted_timeDeriv_eq_pde`; lift linearity transfers it
to the lifted integrands a.e. on `[0,1]`, and the integral splits by linearity. -/
theorem intervalDomain_l2_half_energy_hPDEIntegral_of_integrable
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hA : IntervalIntegrable
        (intervalDomainLift (fun x => u t x * intervalDomain.laplacian (u t) x))
        volume 0 1)
    (hB : IntervalIntegrable
        (intervalDomainLift
          (fun x => u t x * intervalDomain.chemotaxisDiv params (u t) (v t) x))
        volume 0 1)
    (hC : IntervalIntegrable
        (intervalDomainLift
          (fun x => (u t x) ^ 2 * (params.a - params.b * (u t x) ^ params.α)))
        volume 0 1) :
    intervalDomain.integral (intervalDomainL2TimeTerm u t) =
      intervalDomainL2DiffusionIntegral u t -
        params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
        intervalDomainL2LogisticIntegral params u t := by
  classical
  -- Recombine the RHS into a single integral of the lifted combination.
  have hAB : IntervalIntegrable
      (fun y => intervalDomainLift
          (fun x => u t x * intervalDomain.laplacian (u t) x) y -
        params.χ₀ * intervalDomainLift
          (fun x => u t x * intervalDomain.chemotaxisDiv params (u t) (v t) x) y)
      volume 0 1 := hA.sub (hB.const_mul params.χ₀)
  have hcomb :
      (∫ y in (0 : ℝ)..1,
          (intervalDomainLift
              (fun x => u t x * intervalDomain.laplacian (u t) x) y -
            params.χ₀ * intervalDomainLift
              (fun x => u t x * intervalDomain.chemotaxisDiv params (u t) (v t) x) y
            + intervalDomainLift
              (fun x => (u t x) ^ 2 *
                (params.a - params.b * (u t x) ^ params.α)) y))
        = intervalDomainL2DiffusionIntegral u t -
            params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
            intervalDomainL2LogisticIntegral params u t := by
    rw [intervalIntegral.integral_add hAB hC,
      intervalIntegral.integral_sub hA (hB.const_mul params.χ₀),
      intervalIntegral.integral_const_mul]
    rfl
  rw [← hcomb]
  -- LHS: the integral of the lifted time term.
  change intervalDomainIntegral (intervalDomainL2TimeTerm u t) = _
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr_ae ?_
  -- a.e. on `Ι 0 1 = Ioc 0 1` the lifted time term equals the lifted combination;
  -- the only difference is the null endpoint `y = 1`.
  have hne1 : ∀ᵐ y ∂volume, y ≠ (1 : ℝ) := by
    have heq : {y : ℝ | ¬ y ≠ 1} = {(1 : ℝ)} := by ext y; simp
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  filter_upwards [hne1] with y hyne hymem
  rw [Set.uIoc_of_le (zero_le_one)] at hymem
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hymem.1, lt_of_le_of_ne hymem.2 hyne⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  have hxin : (⟨y, hyIcc⟩ : intervalDomain.Point) ∈ intervalDomain.inside := hyIoo
  -- Interior pointwise PDE.
  have hpde := intervalDomain_solution_l2_weighted_timeDeriv_eq_pde hsol ht0 htT hxin
  -- Evaluate all lifts on the interior branch.
  have hlift : ∀ f : intervalDomain.Point → ℝ,
      intervalDomainLift f y = f ⟨y, hyIcc⟩ := by
    intro f; simp [intervalDomainLift, hyIcc]
  simp only [hlift]
  rw [hpde]
  -- `u·(Δu − χ₀ chemDiv + u(a−bu^α)) = u·Δu − χ₀(u·chemDiv) + u²(a−bu^α)`.
  ring

/-! ## Discharging `hA` (the diffusion term) from closed-`C²` regularity -/

/-- **The diffusion integrand `f·Δf` is interval-integrable**, from closed-`[0,1]`
`C²` regularity of `lift f`.  On the interior `(0,1)` the lift of `f·Δf` equals
`(lift f)·(deriv²(lift f))`, which agrees with `(lift f)·(derivWithin²(lift f)
[0,1])` — a product of two functions continuous on the *closed* `[0,1]` (hence
bounded), so the integrand is a.e.-equal on `Ioc 0 1` to a continuous function and
is interval-integrable.  (The ordinary second derivative of the zero-extension is
junk at the endpoints, but `{0,1}`… actually `{1}` in `Ioc`… is null.) -/
theorem intervalDomainLift_diffusion_intervalIntegrable_of_contDiffOn
    {f : intervalDomain.Point → ℝ}
    (hf : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (intervalDomainLift (fun x => f x * intervalDomain.laplacian f x))
      volume 0 1 := by
  classical
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  -- The closed-`[0,1]` second `derivWithin`, continuous on `[0,1]`.
  have hd1 : ContDiffOn ℝ 1
      (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) :=
    hf.derivWithin huniq (le_refl 2)
  have hd2cont : ContinuousOn
      (derivWithin (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) :=
    hd1.continuousOn_derivWithin huniq (le_refl 1)
  -- The continuous-on-`[0,1]` comparison function.
  have hh_cont : ContinuousOn
      (fun y => intervalDomainLift f y *
        derivWithin (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
          (Set.Icc (0 : ℝ) 1) y) (Set.Icc (0 : ℝ) 1) :=
    hf.continuousOn.mul hd2cont
  have hh_int : IntervalIntegrable
      (fun y => intervalDomainLift f y *
        derivWithin (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
          (Set.Icc (0 : ℝ) 1) y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one)]
  -- On the interior, ordinary `deriv²` agrees with the closed `derivWithin²`.
  have hIcc_nhds : ∀ z ∈ Set.Ioo (0 : ℝ) 1, Set.Icc (0 : ℝ) 1 ∈ 𝓝 z :=
    fun z hz => Icc_mem_nhds hz.1 hz.2
  have hinner : Set.EqOn (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
      (deriv (intervalDomainLift f)) (Set.Ioo (0 : ℝ) 1) :=
    fun z hz => derivWithin_of_mem_nhds (hIcc_nhds z hz)
  -- a.e. equality of the lifted integrand with the continuous comparison on `Ioc`.
  have hne1 : ∀ᵐ y ∂volume, y ≠ (1 : ℝ) := by
    have heq : {y : ℝ | ¬ y ≠ 1} = {(1 : ℝ)} := by ext y; simp
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  refine hh_int.congr_ae ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hne1] with y hyne hymem
  rw [Set.uIoc_of_le (zero_le_one)] at hymem
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hymem.1, lt_of_le_of_ne hymem.2 hyne⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  -- LHS: `lift (f·Δf) y = lift f y · deriv²(lift f) y`.
  have hLHS : intervalDomainLift (fun x => f x * intervalDomain.laplacian f x) y
      = intervalDomainLift f y * deriv (deriv (intervalDomainLift f)) y := by
    simp only [intervalDomainLift, hyIcc, dif_pos]
    rfl
  -- The closed `derivWithin²` equals the ordinary `deriv²` at the interior `y`.
  have houter : derivWithin (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
      (Set.Icc (0 : ℝ) 1) y = deriv (deriv (intervalDomainLift f)) y := by
    rw [derivWithin_of_mem_nhds (hIcc_nhds y hyIoo)]
    have hev : derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)
        =ᶠ[𝓝 y] deriv (intervalDomainLift f) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hyIoo) hinner
    exact hev.deriv_eq
  rw [hLHS, houter]

/-- **`hA` for a classical solution**, extracting conjunct (7) at the interior
time `t`. -/
theorem intervalDomainLift_diffusion_intervalIntegrable_of_regularity
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    IntervalIntegrable
      (intervalDomainLift (fun x => u t x * intervalDomain.laplacian (u t) x))
      volume 0 1 :=
  intervalDomainLift_diffusion_intervalIntegrable_of_contDiffOn
    (hsol.regularity.2.2.2.2.2.2.1 t ht).1.1

/-! ## Discharging `hC` (the logistic term) from regularity + positivity -/

/-- **The logistic integrand `u²(a−bu^α)` is interval-integrable**, from conjunct
(7) closed-`C²` (continuity of `lift u` on `[0,1]`) and the solution positivity
`u > 0`.  On `[0,1]` the lift of `u²(a−bu^α)` equals `(lift u)²·(a − b·(lift u)^α)`,
continuous because `lift u` is continuous and strictly positive there (so the real
power `(lift u)^α` is continuous via `ContinuousOn.rpow_const`). -/
theorem intervalDomainLift_logistic_intervalIntegrable_of_regularity
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x => (u t x) ^ 2 * (params.a - params.b * (u t x) ^ params.α)))
      volume 0 1 := by
  classical
  have hreg7 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hcont_u : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    hreg7.continuousOn
  -- `lift u` is strictly positive on `[0,1]` (positivity at every point).
  have hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u t) y ≠ 0 := by
    intro y hy
    have : intervalDomainLift (u t) y = u t ⟨y, hy⟩ := by simp [intervalDomainLift, hy]
    rw [this]; exact ne_of_gt (hsol.u_pos' ht0 htT)
  -- The continuous comparison function on `[0,1]`.
  have hpow : ContinuousOn (fun y => (intervalDomainLift (u t) y) ^ params.α)
      (Set.Icc (0 : ℝ) 1) :=
    hcont_u.rpow_const (fun y hy => Or.inl (hpos y hy))
  have hcomp : ContinuousOn
      (fun y => (intervalDomainLift (u t) y) ^ 2 *
        (params.a - params.b * (intervalDomainLift (u t) y) ^ params.α))
      (Set.Icc (0 : ℝ) 1) :=
    (hcont_u.pow 2).mul (continuousOn_const.sub (continuousOn_const.mul hpow))
  -- The lifted integrand agrees with the comparison on `[0,1]`.
  have hEq : Set.EqOn
      (intervalDomainLift
        (fun x => (u t x) ^ 2 * (params.a - params.b * (u t x) ^ params.α)))
      (fun y => (intervalDomainLift (u t) y) ^ 2 *
        (params.a - params.b * (intervalDomainLift (u t) y) ^ params.α))
      (Set.Icc (0 : ℝ) 1) := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (zero_le_one)]
  exact hcomp.congr hEq

/-! ## Factoring `hB`: the `u` multiplier is continuous (bounded) -/

/-- The lift of a pointwise product is the product of the lifts (everywhere on
`ℝ`). -/
theorem intervalDomainLift_mul (f g : intervalDomain.Point → ℝ) (y : ℝ) :
    intervalDomainLift (fun x => f x * g x) y
      = intervalDomainLift f y * intervalDomainLift g y := by
  unfold intervalDomainLift
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1 <;> simp [hy]

/-- **`hB` factored: it suffices that the chemotaxis divergence itself is
interval-integrable.**  The diffusion-energy chemotaxis integrand `u·chemDiv`
factors, on `[0,1]`, as the product of `lift u` (continuous on the compact
`[0,1]` by conjunct (7), hence bounded) and `lift chemDiv`; a continuous-times-
integrable product on a compact interval is interval-integrable.  This removes the
`u` entanglement: the only residual is the interval-integrability of the
chemotaxis flux divergence `∂ₓ(u·∂ₓv/(1+v)^β)` itself — the genuine `v`-coupled
frontier (`v ∈ C²`, `1+v ≥ 1 > 0` from `v_nonneg`). -/
theorem intervalDomainLift_chemotaxis_intervalIntegrable_of_chemDiv
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hchem : IntervalIntegrable
        (intervalDomainLift (intervalDomain.chemotaxisDiv params (u t) (v t)))
        volume 0 1) :
    IntervalIntegrable
      (intervalDomainLift
        (fun x => u t x * intervalDomain.chemotaxisDiv params (u t) (v t) x))
      volume 0 1 := by
  have hcont_u : ContinuousOn (intervalDomainLift (u t)) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact (hsol.regularity.2.2.2.2.2.2.1 t ht).1.1.continuousOn
  have hfun : intervalDomainLift
      (fun x => u t x * intervalDomain.chemotaxisDiv params (u t) (v t) x)
      = fun y => intervalDomainLift (u t) y *
        intervalDomainLift (intervalDomain.chemotaxisDiv params (u t) (v t)) y := by
    funext y; exact intervalDomainLift_mul _ _ y
  rw [hfun]
  exact hchem.continuousOn_mul hcont_u

/-! ## Discharging the chemotaxis flux divergence integrability (the `v`-coupled
core) -/

/-- **`C¹`-up-to-boundary of the chemotaxis flux quotient.**  With `lift u`,
`lift v` both `C²` on `[0,1]` (conjunct (7)) and `1+lift v ≥ 1 > 0` (`v ≥ 0`), the
quotient `q̃ = (lift u)·(derivWithin (lift v) [0,1])/(1+lift v)^β` — the
closed-`[0,1]` version of the chemotaxis flux — is `C¹` on `[0,1]`.  The numerator
is a product of `C¹` factors (`lift u`, and `derivWithin (lift v) [0,1]` which is
`C¹` since `lift v` is `C²`), and the denominator is `C¹` and nonzero
(`z ↦ z^β` is `C^∞` away from `0`, composed with the positive `C²` base
`1+lift v`). -/
theorem intervalDomainChemotaxisQuotient_contDiffOn_one_of_regularity
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContDiffOn ℝ 1
      (fun y => intervalDomainLift (u t) y *
        derivWithin (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) y /
        (1 + intervalDomainLift (v t) y) ^ params.β) (Set.Icc (0 : ℝ) 1) := by
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hv2 : ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2.1 t ⟨ht0, htT⟩).2.1
  -- Numerator: `lift u · derivWithin (lift v) Icc`, a product of `C¹` factors.
  have hu1 : ContDiffOn ℝ 1 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    hu2.of_le (by norm_num)
  have hdv1 : ContDiffOn ℝ 1
      (derivWithin (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) :=
    hv2.derivWithin huniq (by norm_num)
  have hnum : ContDiffOn ℝ 1
      (fun y => intervalDomainLift (u t) y *
        derivWithin (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) y) (Set.Icc (0 : ℝ) 1) :=
    hu1.mul hdv1
  -- Positivity of the denominator base `1 + lift v ≥ 1`.
  have hbase_pos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + intervalDomainLift (v t) y := by
    intro y hy
    have hvnn : 0 ≤ intervalDomainLift (v t) y := by
      have : intervalDomainLift (v t) y = v t ⟨y, hy⟩ := by simp [intervalDomainLift, hy]
      rw [this]; exact hsol.v_nonneg ht0 htT
    linarith
  -- Denominator base is `C¹`.
  have hbase1 : ContDiffOn ℝ 1 (fun y => 1 + intervalDomainLift (v t) y)
      (Set.Icc (0 : ℝ) 1) := contDiffOn_const.add (hv2.of_le (by norm_num))
  -- `z ↦ z^β` is `C¹` on `Ioi 0`.
  have hrpow : ContDiffOn ℝ 1 (fun z : ℝ => z ^ params.β) (Set.Ioi (0 : ℝ)) :=
    fun z hz => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hz)).contDiffWithinAt
  -- Denominator `(1+lift v)^β` is `C¹` (composition).
  have hden : ContDiffOn ℝ 1 (fun y => (1 + intervalDomainLift (v t) y) ^ params.β)
      (Set.Icc (0 : ℝ) 1) :=
    hrpow.comp hbase1 (fun y hy => hbase_pos y hy)
  have hden_ne : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (1 + intervalDomainLift (v t) y) ^ params.β ≠ 0 :=
    fun y hy => ne_of_gt (Real.rpow_pos_of_pos (hbase_pos y hy) _)
  exact hnum.div hden hden_ne

/-- **The chemotaxis flux divergence is interval-integrable**, from closed-`C²`
regularity of `u, v` and `v ≥ 0`.  Mirrors the diffusion-term argument: on the
interior the divergence `∂ₓ` of the chemotaxis flux equals the ordinary derivative
of the flux quotient `q`, which agrees on the open interior with the closed
version `q̃` (the two differ only in `deriv (lift v)` vs `derivWithin (lift v)
[0,1]`, equal on the interior); `q̃` is `C¹` up to the boundary, so `derivWithin q̃
[0,1]` is continuous on `[0,1]`, and the divergence agrees with it a.e. on
`Ioc 0 1`. -/
theorem intervalDomainLift_chemDiv_intervalIntegrable_of_regularity
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift (intervalDomain.chemotaxisDiv params (u t) (v t)))
      volume 0 1 := by
  classical
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  -- The closed flux quotient `q̃` and its `C¹` regularity.
  set qt : ℝ → ℝ := fun y => intervalDomainLift (u t) y *
    derivWithin (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) y /
    (1 + intervalDomainLift (v t) y) ^ params.β with hqt_def
  have hqt : ContDiffOn ℝ 1 qt (Set.Icc (0 : ℝ) 1) :=
    intervalDomainChemotaxisQuotient_contDiffOn_one_of_regularity hsol ht0 htT
  -- The interior flux quotient `q` (using ordinary `deriv (lift v)`).
  set q : ℝ → ℝ := fun y => intervalDomainLift (u t) y *
    deriv (intervalDomainLift (v t)) y /
    (1 + intervalDomainLift (v t) y) ^ params.β with hq_def
  -- `derivWithin q̃ [0,1]` is continuous on `[0,1]`.
  have hd_cont : ContinuousOn (derivWithin qt (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) :=
    hqt.continuousOn_derivWithin huniq (le_refl 1)
  have hd_int : IntervalIntegrable (derivWithin qt (Set.Icc (0 : ℝ) 1)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le (zero_le_one)]
  -- On the interior, `deriv (lift v)` agrees with `derivWithin (lift v) [0,1]`,
  -- hence `q = q̃` there.
  have hIcc_nhds : ∀ z ∈ Set.Ioo (0 : ℝ) 1, Set.Icc (0 : ℝ) 1 ∈ 𝓝 z :=
    fun z hz => Icc_mem_nhds hz.1 hz.2
  have hqq : Set.EqOn q qt (Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    have hvz : deriv (intervalDomainLift (v t)) z
        = derivWithin (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) z :=
      (derivWithin_of_mem_nhds (hIcc_nhds z hz)).symm
    simp only [hq_def, hqt_def, hvz]
  -- a.e. equality of the lifted divergence with `derivWithin q̃ [0,1]` on `Ioc`.
  have hne1 : ∀ᵐ y ∂volume, y ≠ (1 : ℝ) := by
    have heq : {y : ℝ | ¬ y ≠ 1} = {(1 : ℝ)} := by ext y; simp
    rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
  refine hd_int.congr_ae ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hne1] with y hyne hymem
  rw [Set.uIoc_of_le (zero_le_one)] at hymem
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hymem.1, lt_of_le_of_ne hymem.2 hyne⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hyIoo
  -- LHS: `lift chemDiv y = deriv q y`.
  have hLHS : intervalDomainLift (intervalDomain.chemotaxisDiv params (u t) (v t)) y
      = deriv q y := by
    simp only [intervalDomainLift, hyIcc, dif_pos]
    rfl
  -- `deriv q y = derivWithin q̃ [0,1] y` at the interior `y`.
  have hderiv : deriv q y = derivWithin qt (Set.Icc (0 : ℝ) 1) y := by
    have hev : q =ᶠ[𝓝 y] qt :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hyIoo) hqq
    rw [hev.deriv_eq, derivWithin_of_mem_nhds (hIcc_nhds y hyIoo)]
  rw [hLHS, hderiv]

/-! ## Status: `hPDEIntegral` is now fully reducible from regularity + positivity

All three integrability inputs of
`intervalDomain_l2_half_energy_hPDEIntegral_of_integrable` are discharged from the
data every classical solution carries:

* `hA` — `intervalDomainLift_diffusion_intervalIntegrable_of_regularity`;
* `hC` — `intervalDomainLift_logistic_intervalIntegrable_of_regularity`;
* `hB` — `intervalDomainLift_chemotaxis_intervalIntegrable_of_chemDiv`
  composed with `intervalDomainLift_chemDiv_intervalIntegrable_of_regularity`.

`intervalDomain_l2_half_energy_hPDEIntegral_of_regularity` below assembles them.
-/

/-- **`hPDEIntegral`, UNCONDITIONALLY from regularity + positivity.**  Every
classical solution at an interior time satisfies the PDE-substitution identity:
all three integrability inputs are discharged from conjunct (7) closed-`C²`,
strict positivity `u > 0`, and `v ≥ 0`. -/
theorem intervalDomain_l2_half_energy_hPDEIntegral_of_regularity
    {params : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral (intervalDomainL2TimeTerm u t) =
      intervalDomainL2DiffusionIntegral u t -
        params.χ₀ * intervalDomainL2ChemotaxisIntegral params u v t +
        intervalDomainL2LogisticIntegral params u t :=
  intervalDomain_l2_half_energy_hPDEIntegral_of_integrable hsol ht0 htT
    (intervalDomainLift_diffusion_intervalIntegrable_of_regularity hsol ⟨ht0, htT⟩)
    (intervalDomainLift_chemotaxis_intervalIntegrable_of_chemDiv hsol ⟨ht0, htT⟩
      (intervalDomainLift_chemDiv_intervalIntegrable_of_regularity hsol ht0 htT))
    (intervalDomainLift_logistic_intervalIntegrable_of_regularity hsol ht0 htT)

/-! ## (Former) status of the remaining integrability input

`intervalDomain_l2_half_energy_hPDEIntegral_of_integrable` reduces `hPDEIntegral`
to `hA`, `hB`, `hC`.  `hA` (diffusion) and `hC` (logistic) are **discharged** from
the regularity conjunct (7) + positivity
(`intervalDomainLift_{diffusion,logistic}_intervalIntegrable_of_regularity`).  `hB`
is **factored** (`intervalDomainLift_chemotaxis_intervalIntegrable_of_chemDiv`): the
`u` multiplier is continuous/bounded, so `hB` follows from the interval-
integrability of the chemotaxis flux divergence alone.  The single remaining
integrability input is therefore:

* **interval-integrability of `∂ₓ(u·∂ₓv/(1+v)^β)`** — the chemotaxis flux
  divergence, coupling to `v`'s `C²` regularity and `1+v ≥ 1 > 0` (`v ≥ 0`,
  `IsPaper2ClassicalSolution.v_nonneg`); the genuine `v`-coupled frontier.  It
  needs the quotient `q = (lift u)·(∂ₓ lift v)/(1+lift v)^β` to be `C¹` up to the
  boundary (so `∂ₓ q` is bounded/integrable), via `ContDiffOn.div` +
  `contDiffAt_rpow_const_of_ne` + `ContDiffOn.derivWithin`.

This is recorded as the precise residual of `hPDEIntegral`, NOT faked.
-/

end

end ShenWork.Paper2
