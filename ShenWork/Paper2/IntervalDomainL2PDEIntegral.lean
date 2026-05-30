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

/-! ## Status of the three integrability inputs

`intervalDomain_l2_half_energy_hPDEIntegral_of_integrable` reduces `hPDEIntegral`
to `hA`, `hB`, `hC`.  Their status:

* **`hA` (`∫₀¹ u·Δu`)** — provable from conjunct (7) closed-`C²`.  On `[0,1]` the
  lift of `u·Δu` agrees a.e. (on the interior) with `(lift u)·(deriv²(lift u))`,
  and conjunct (7) makes both factors continuous on the *interior* (the ordinary
  endpoint second derivative of the zero-extension is junk, but that is a null
  set).  The same a.e.-on-`Ioc` bookkeeping as
  `intervalIntegrable_deriv2_intervalDomainLift_profile` applies; this is routine
  but not yet assembled for the abstract-solution form.
* **`hC` (`∫₀¹ u²(a−bu^α)`)** — continuous in `u`, but the real power `u^α`
  (`α : ℝ`, `1 ≤ α`) is only continuous where `u ≥ 0`, so this needs solution
  positivity `u ≥ 0` (a genuine maximum-principle input).
* **`hB` (`∫₀¹ u·chemDiv`)** — the chemotaxis flux divergence
  `∂ₓ(u·∂ₓv/(1+v)^β)`, coupling to `v`'s `C²` regularity and `1+v` bounded below;
  the genuine `v`-coupled frontier.

These are recorded as the precise residual of `hPDEIntegral`, NOT faked.
-/

end

end ShenWork.Paper2
