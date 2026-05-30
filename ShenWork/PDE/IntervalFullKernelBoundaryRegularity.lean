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

end ShenWork.IntervalFullKernelRegularity
