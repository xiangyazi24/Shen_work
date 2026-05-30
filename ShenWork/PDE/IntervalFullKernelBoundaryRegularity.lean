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

/-! ## Up-to-boundary `C¹` continuity of the semigroup-profile spatial derivative -/

/-- The full propagator equals, **as a function on all of `ℝ`**, the cosine
spectral heat value of its coefficients (the `hx : Ioo 0 1` of
`intervalFullSemigroupOperator_eq_cosineHeatValue` is unused). -/
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_funext
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Continuous f)
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    (fun x => intervalFullSemigroupOperator t f x) =
      fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x := by
  funext x
  rw [intervalFullSemigroupOperator]
  rw [show (fun y => intervalNeumannFullKernel t x y * f y)
        = (fun y => (∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
            (Real.cos ((m : ℝ) * Real.pi * x) *
              Real.cos ((m : ℝ) * Real.pi * y))) * f y) from by
      funext y; rw [hkernel x y]]
  exact ShenWork.IntervalFullKernelInterchange.fullKernelIntegralInterchange_holds t ht f hf x

/-- **Up-to-boundary `C¹` continuity of the semigroup profile derivative.**
For a semigroup-profile slice (`lift g = S_t f` on `[0,1]`), the *ordinary*
spatial derivative `deriv (lift g)` is continuous on the **closed** `[0,1]`.

On the interior it agrees with `deriv (S_t f)` (continuous, since `S_t f ∈ C²`);
at the endpoints both vanish — `deriv (lift g) = 0` by
`deriv_intervalDomainLift_eq_zero_at_{zero,one}` and `deriv (S_t f) = 0` by the
Neumann property of the cosine profile
(`unitIntervalCosineHeatValue_deriv_zero_at_endpoint`). -/
theorem deriv_intervalDomainLift_continuousOn_Icc_of_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    ContinuousOn (deriv (intervalDomainLift g)) (Set.Icc (0 : ℝ) 1) := by
  set S : ℝ → ℝ := fun x => intervalFullSemigroupOperator t f x with hS
  have hid : S = fun x => unitIntervalCosineHeatValue t (cosineCoeffs f) x :=
    intervalFullSemigroupOperator_eq_cosineHeatValue_funext t ht f hf hkernel
  have hC2 :
      ContDiff ℝ 2 S :=
    ShenWork.IntervalFullKernelInterchange.intervalFullSemigroupOperator_contDiff_two_unconditional
      t ht f hf hM hkernel
  have hderiv_cont : Continuous (deriv S) := hC2.continuous_deriv (by norm_num)
  have hd0 : deriv S 0 = 0 := by
    rw [hid]; exact unitIntervalCosineHeatValue_deriv_zero_at_endpoint ht hM (Or.inl rfl)
  have hd1 : deriv S 1 = 0 := by
    rw [hid]; exact unitIntervalCosineHeatValue_deriv_zero_at_endpoint ht hM (Or.inr rfl)
  have hEqD : Set.EqOn (deriv (intervalDomainLift g)) (deriv S) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · subst hx0; rw [deriv_intervalDomainLift_eq_zero_at_zero, hd0]
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · rw [hx1, deriv_intervalDomainLift_eq_zero_at_one, hd1]
      · -- interior point: `lift g =ᶠ S` on the open `(0,1)`
        have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
        have hev : intervalDomainLift g =ᶠ[𝓝 x] S :=
          Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hxIoo)
            (fun y hy => hg ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
        exact hev.deriv_eq
  exact (hderiv_cont.continuousOn).congr hEqD

/-! ## The remaining T4-b regularity-package pieces for a semigroup profile

Below, `S := fun x => intervalFullSemigroupOperator t f x` is `ContDiff ℝ 2` on all
of `ℝ`, and `lift g = S` on `[0,1]`.  On the **open** interior `(0,1)` the lift and
all its derivatives agree with `S`'s (an open-set congruence), which yields the
interior `HasDerivWithinAt` data and the interval-integrability of the first and
second derivatives. -/

/-- On the open interior, the first lift derivative agrees with `deriv S`. -/
theorem deriv_intervalDomainLift_eqOn_Ioo_of_semigroup
    {t : ℝ} {f : ℝ → ℝ}
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1)) :
    Set.EqOn (deriv (intervalDomainLift g))
      (deriv (fun x => intervalFullSemigroupOperator t f x)) (Set.Ioo (0 : ℝ) 1) := by
  intro y hy
  have hev : intervalDomainLift g =ᶠ[𝓝 y]
      (fun x => intervalFullSemigroupOperator t f x) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
      (fun z hz => hg ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
  exact hev.deriv_eq

/-- Closed-`[0,1]` continuity of the lift itself (the `C⁰` package piece). -/
theorem intervalDomainLift_continuousOn_Icc_of_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    ContinuousOn (intervalDomainLift g) (Set.Icc (0 : ℝ) 1) :=
  (intervalFullSemigroupProfile_contDiffOn_two_closed ht hf hM hg hkernel).continuousOn

/-- Interior right-`HasDerivWithinAt` of the lift (`test`/`f` first-order datum). -/
theorem intervalDomainLift_hasDerivWithinAt_Ioi_of_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (intervalDomainLift g)
      (deriv (intervalDomainLift g) x) (Set.Ioi x) x := by
  have hC2 :
      ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator t f x) :=
    ShenWork.IntervalFullKernelInterchange.intervalFullSemigroupOperator_contDiff_two_unconditional
      t ht f hf hM hkernel
  have hev : intervalDomainLift g =ᶠ[𝓝 x]
      (fun z => intervalFullSemigroupOperator t f z) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
      (fun z hz => hg ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
  have hdiff : DifferentiableAt ℝ (intervalDomainLift g) x :=
    (hC2.differentiable (by norm_num)).differentiableAt.congr_of_eventuallyEq hev
  exact hdiff.hasDerivAt.hasDerivWithinAt

/-- Interior right-`HasDerivWithinAt` of the first derivative (second-order datum). -/
theorem deriv_intervalDomainLift_hasDerivWithinAt_Ioi_of_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y)))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (deriv (intervalDomainLift g))
      (deriv (deriv (intervalDomainLift g)) x) (Set.Ioi x) x := by
  have hC2 :
      ContDiff ℝ 2 (fun x => intervalFullSemigroupOperator t f x) :=
    ShenWork.IntervalFullKernelInterchange.intervalFullSemigroupOperator_contDiff_two_unconditional
      t ht f hf hM hkernel
  have hevD : deriv (intervalDomainLift g) =ᶠ[𝓝 x]
      deriv (fun z => intervalFullSemigroupOperator t f z) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
      (fun z hz => deriv_intervalDomainLift_eqOn_Ioo_of_semigroup hg hz)
  have hdiff : DifferentiableAt ℝ (deriv (intervalDomainLift g)) x :=
    ((hC2.deriv' (n := 1)).differentiable (by norm_num)).differentiableAt.congr_of_eventuallyEq
      hevD
  exact hdiff.hasDerivAt.hasDerivWithinAt

/-- First lift derivative is interval-integrable on `[0,1]` (from `C¹` continuity). -/
theorem intervalIntegrable_deriv_intervalDomainLift_of_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    IntervalIntegrable (deriv (intervalDomainLift g)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (zero_le_one)]
  exact deriv_intervalDomainLift_continuousOn_Icc_of_semigroup ht hf hM hg hkernel

/-- Second lift derivative is interval-integrable on `[0,1]`: it equals `deriv² S`
on the interior (full measure on `[0,1]`), and `deriv² S` is continuous. -/
theorem intervalIntegrable_deriv2_intervalDomainLift_of_semigroup
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M)
    {g : intervalDomainPoint → ℝ}
    (hg : Set.EqOn (intervalDomainLift g)
      (fun x => intervalFullSemigroupOperator t f x) (Set.Icc (0 : ℝ) 1))
    (hkernel : ∀ x : ℝ, ∀ y,
      intervalNeumannFullKernel t x y =
        ∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) :
    IntervalIntegrable (deriv (deriv (intervalDomainLift g)))
      MeasureTheory.volume 0 1 := by
  set S : ℝ → ℝ := fun x => intervalFullSemigroupOperator t f x with hS
  have hC2 : ContDiff ℝ 2 S :=
    ShenWork.IntervalFullKernelInterchange.intervalFullSemigroupOperator_contDiff_two_unconditional
      t ht f hf hM hkernel
  have hd2S_cont : Continuous (deriv (deriv S)) :=
    (hC2.deriv' (n := 1)).continuous_deriv (by norm_num)
  have hd2S_int : IntervalIntegrable (deriv (deriv S)) MeasureTheory.volume 0 1 :=
    hd2S_cont.intervalIntegrable 0 1
  -- second derivatives agree on the interior `(0,1)`, full measure on `[0,1]`.
  have hEq2 : Set.EqOn (deriv (deriv (intervalDomainLift g))) (deriv (deriv S))
      (Set.Ioo (0 : ℝ) 1) := by
    intro y hy
    have hevD : deriv (intervalDomainLift g) =ᶠ[𝓝 y] deriv S :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy)
        (fun z hz => deriv_intervalDomainLift_eqOn_Ioo_of_semigroup hg hz)
    exact hevD.deriv_eq
  have hae : deriv (deriv (intervalDomainLift g)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)]
      deriv (deriv S) := by
    rw [Set.uIoc_of_le (zero_le_one)]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    have hne1 : ∀ᵐ y ∂MeasureTheory.volume, y ≠ (1 : ℝ) := by
      have heq : {y : ℝ | ¬ y ≠ 1} = {(1 : ℝ)} := by ext y; simp [eq_comm]
      rw [MeasureTheory.ae_iff, heq]; exact Real.volume_singleton
    filter_upwards [hne1] with y hyne hyIoc
    exact hEq2 ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hyne⟩
  exact hd2S_int.congr_ae hae.symm

end ShenWork.IntervalFullKernelRegularity
