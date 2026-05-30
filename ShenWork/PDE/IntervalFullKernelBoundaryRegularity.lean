/-
  ShenWork/PDE/IntervalFullKernelBoundaryRegularity.lean

  **T5 — parabolic boundary regularity (up to the spatial endpoints).**

  Closed-boundary (`Icc 0 1`) spatial regularity of the full-Neumann-kernel
  semigroup profile, discharging the **closed**-`C²` content of conjunct (7) of
  `intervalDomainClassicalRegularity` for pure-semigroup time slices.

  The interior version (`intervalFullSemigroupProfile_contDiffOn_two`, on
  `Ioo 0 1`) is upgraded to the closed interval `Icc 0 1` using the fact that the
  operator↔cosine-spectral-heat-value identity holds at **every** `x ∈ ℝ` (the
  `hx : Ioo 0 1` of `intervalFullSemigroupOperator_eq_cosineHeatValue` is unused),
  so the full propagator is `ContDiff ℝ 2` on all of `ℝ`
  (`intervalFullSemigroupOperator_contDiff_two_unconditional`) and the lifted
  profile inherits `ContDiffOn ℝ 2` on the closed boundary by congruence.

  This is the spatial half of the up-to-boundary `C^{2,1}` regularity (the rest —
  the Duhamel source term and the time derivative — is attacked in companion
  files).  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelRegularity

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalFullKernelRegularity

open ShenWork.IntervalDomain ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalDomainRegularityBootstrap

/-- **Closed-boundary `C²` of the full-kernel semigroup profile.**  If a function
`g : intervalDomainPoint → ℝ` agrees, after the zero-extension lift, with the
full-kernel Neumann semigroup `f ↦ S_t f` of a continuous bounded-coefficient `f`
on the **closed** interval `[0,1]`, then its lift is `ContDiffOn ℝ 2` on `[0,1]`
— continuous second spatial derivative **up to and including** the Neumann
endpoints.

Upgrade of `intervalFullSemigroupProfile_contDiffOn_two` from `Ioo 0 1` to
`Icc 0 1`: the propagator is `ContDiff ℝ 2` on all of `ℝ`
(`intervalFullSemigroupOperator_contDiff_two_unconditional`), and the lifted
profile inherits `ContDiffOn` on `[0,1]` by `ContDiffOn.congr`. -/
theorem intervalFullSemigroupProfile_contDiffOn_two_closed
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    ContDiffOn ℝ 2 (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) := by
  have hC2 :=
    ShenWork.IntervalFullKernelInterchange.intervalFullSemigroupOperator_contDiff_two_unconditional
      t ht f hf hM hkernel
  exact (hC2.contDiffOn).congr hg

/-- **Closed-boundary `C²` conjunct (7) for full-kernel semigroup profiles.**
If for every interior time `t ∈ (0,T)` both slices `u t`, `v t` lift to functions
agreeing on the **closed** `[0,1]` with full-kernel semigroup propagators of
continuous bounded-coefficient sources, then the closed-`C²` part of conjunct (7)
of `intervalDomainClassicalRegularity` holds. -/
theorem intervalFullSemigroupProfile_classicalRegularity_closedC2
    {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hu : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ f : ℝ → ℝ, Continuous f ∧
      ∃ M : ℝ, (∀ n, |cosineCoeffs f n| ≤ M) ∧
        Set.EqOn (intervalDomainLift (u t))
          (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1) ∧
        (∀ x : ℝ, ∀ y, intervalNeumannFullKernel t x y =
          ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
            (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))))
    (hv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ f : ℝ → ℝ, Continuous f ∧
      ∃ M : ℝ, (∀ n, |cosineCoeffs f n| ≤ M) ∧
        Set.EqOn (intervalDomainLift (v t))
          (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1) ∧
        (∀ x : ℝ, ∀ y, intervalNeumannFullKernel t x y =
          ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
            (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)))) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) ∧
        ContDiffOn ℝ 2 (intervalDomainLift (v t)) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  have htpos : 0 < t := ht.1
  obtain ⟨fu, hfu_cont, Mu, hMu, hu_eq, hu_ker⟩ := hu t ht
  obtain ⟨fv, hfv_cont, Mv, hMv, hv_eq, hv_ker⟩ := hv t ht
  exact ⟨intervalFullSemigroupProfile_contDiffOn_two_closed htpos hfu_cont hMu hu_eq hu_ker,
    intervalFullSemigroupProfile_contDiffOn_two_closed htpos hfv_cont hMv hv_eq hv_ker⟩

/-! ## Unconditional endpoint vanishing of the ordinary lift derivative

For **any** `g : intervalDomainPoint → ℝ`, the *ordinary* (two-sided) derivative of
the zero-extension lift vanishes at both endpoints `0, 1`.  Reason: the lift is
identically `0` on the exterior ray (`Iio 0` resp. `Ioi 1`), so its one-sided
derivative there is `0`; either the lift is not differentiable at the endpoint
(`deriv = 0` by convention) or it is, in which case continuity forces the endpoint
value to `0` and the (unique) derivative equals the exterior one-sided derivative
`0`.  This discharges the `deriv (lift (u t)) {0,1} = 0` half of conjunct (7) of
`intervalDomainClassicalRegularity` for *every* solution, and supplies the
endpoint identification used by the energy IBP (T4). -/

/-- The ordinary lift derivative vanishes at the left endpoint, for any `g`. -/
theorem deriv_intervalDomainLift_eq_zero_at_zero (g : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift g) 0 = 0 := by
  by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift g) (0 : ℝ)
  · have hev0 : intervalDomainLift g =ᶠ[nhdsWithin (0 : ℝ) (Set.Iio 0)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxlt : x < 0 := hx
      simp only [intervalDomainLift]
      rw [dif_neg (fun h => absurd h.1 (not_le.mpr hxlt))]
    have hval : intervalDomainLift g (0 : ℝ) = 0 := by
      have hL : Filter.Tendsto (intervalDomainLift g)
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) :=
        (Filter.tendsto_congr' hev0).mpr tendsto_const_nhds
      have hC : Filter.Tendsto (intervalDomainLift g)
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 (intervalDomainLift g 0)) :=
        hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique hC hL
    have h2 : HasDerivWithinAt (intervalDomainLift g) 0 (Set.Iio 0) 0 :=
      (hasDerivWithinAt_const (c := (0 : ℝ)) (s := Set.Iio (0 : ℝ)) (x := (0 : ℝ))).congr_of_eventuallyEq
        hev0 hval
    have h1 : HasDerivWithinAt (intervalDomainLift g)
        (deriv (intervalDomainLift g) 0) (Set.Iio 0) 0 :=
      hdiff.hasDerivAt.hasDerivWithinAt
    exact (uniqueDiffWithinAt_Iio 0).eq_deriv _ h1 h2
  · exact deriv_zero_of_not_differentiableAt hdiff

/-- The ordinary lift derivative vanishes at the right endpoint, for any `g`. -/
theorem deriv_intervalDomainLift_eq_zero_at_one (g : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift g) 1 = 0 := by
  by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift g) (1 : ℝ)
  · have hev1 : intervalDomainLift g =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxgt : 1 < x := hx
      simp only [intervalDomainLift]
      rw [dif_neg (fun h => absurd h.2 (not_le.mpr hxgt))]
    have hval : intervalDomainLift g (1 : ℝ) = 0 := by
      have hL : Filter.Tendsto (intervalDomainLift g)
          (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 0) :=
        (Filter.tendsto_congr' hev1).mpr tendsto_const_nhds
      have hC : Filter.Tendsto (intervalDomainLift g)
          (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (intervalDomainLift g 1)) :=
        hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique hC hL
    have h2 : HasDerivWithinAt (intervalDomainLift g) 0 (Set.Ioi 1) 1 :=
      (hasDerivWithinAt_const (c := (0 : ℝ)) (s := Set.Ioi (1 : ℝ)) (x := (1 : ℝ))).congr_of_eventuallyEq
        hev1 hval
    have h1 : HasDerivWithinAt (intervalDomainLift g)
        (deriv (intervalDomainLift g) 1) (Set.Ioi 1) 1 :=
      hdiff.hasDerivAt.hasDerivWithinAt
    exact (uniqueDiffWithinAt_Ioi 1).eq_deriv _ h1 h2
  · exact deriv_zero_of_not_differentiableAt hdiff

end ShenWork.IntervalFullKernelRegularity
