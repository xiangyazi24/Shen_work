/-
  Statement layer for Chen-Ruau-Shen,
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type
  source, I: Boundedness and global existence".

  This file introduces a bounded-domain PDE interface and states the paper's
  main results against that interface.  It deliberately does not reuse the toy
  predicates in `Paper2/Defs.lean`.
-/
import ShenWork.Paper2.Defs
import ShenWork.PDE.BoundedDomainData
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.IntervalDomainMaxPrinciple
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Filter Topology

namespace ShenWork.Paper2

noncomputable section

def positivePart (r : ℝ) : ℝ := max r 0

lemma positivePart_nonneg (r : ℝ) : 0 ≤ positivePart r := by
  exact le_max_right r 0

lemma le_positivePart (r : ℝ) : r ≤ positivePart r := by
  exact le_max_left r 0

lemma positivePart_eq_self_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    positivePart r = r := by
  simp [positivePart, hr]

lemma positivePart_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    positivePart r = 0 := by
  simp [positivePart, hr]

lemma positivePart_eq_zero_iff {r : ℝ} :
    positivePart r = 0 ↔ r ≤ 0 := by
  constructor
  · intro h
    have hr : r ≤ positivePart r := le_positivePart r
    linarith
  · exact positivePart_eq_zero_of_nonpos

lemma positivePart_pos_iff {r : ℝ} :
    0 < positivePart r ↔ 0 < r := by
  constructor
  · intro h
    by_contra hn
    have hzero : positivePart r = 0 :=
      positivePart_eq_zero_of_nonpos (le_of_not_gt hn)
    linarith
  · intro hr
    have hle : r ≤ positivePart r := le_positivePart r
    linarith

lemma positivePart_eq_self_iff {r : ℝ} :
    positivePart r = r ↔ 0 ≤ r := by
  constructor
  · intro h
    rw [← h]
    exact positivePart_nonneg r
  · exact positivePart_eq_self_of_nonneg


def IsPaper2ClassicalSolution
    (D : BoundedDomainData) (p : CM2Params) (T : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  0 < T ∧
    D.classicalRegularity T u v ∧
    (∀ t x, 0 < t → t < T → x ∈ D.inside → 0 < u t x) ∧
    (∀ t x, 0 < t → t < T → x ∈ D.inside →
      D.timeDeriv u t x =
        D.laplacian (u t) x
          - p.χ₀ * D.chemotaxisDiv p (u t) (v t) x
          + u t x * (p.a - p.b * (u t x) ^ p.α)) ∧
    (∀ t x, 0 < t → t < T → x ∈ D.inside →
      0 = D.laplacian (v t) x - p.μ * v t x + p.ν * (u t x) ^ p.γ) ∧
    (∀ t x, 0 < t → t < T → x ∈ D.boundary →
      D.normalDeriv (u t) x = 0 ∧ D.normalDeriv (v t) x = 0)

def IsPaper2GlobalClassicalSolution
    (D : BoundedDomainData) (p : CM2Params)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ T > 0, IsPaper2ClassicalSolution D p T u v

lemma IsPaper2ClassicalSolution.of_components
    {D : BoundedDomainData} {p : CM2Params} {T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (hT : 0 < T)
    (hreg : D.classicalRegularity T u v)
    (hpos :
      ∀ t x, 0 < t → t < T → x ∈ D.inside → 0 < u t x)
    (hpde_u :
      ∀ t x, 0 < t → t < T → x ∈ D.inside →
        D.timeDeriv u t x =
          D.laplacian (u t) x
            - p.χ₀ * D.chemotaxisDiv p (u t) (v t) x
            + u t x * (p.a - p.b * (u t x) ^ p.α))
    (hpde_v :
      ∀ t x, 0 < t → t < T → x ∈ D.inside →
        0 = D.laplacian (v t) x - p.μ * v t x + p.ν * (u t x) ^ p.γ)
    (hneumann :
      ∀ t x, 0 < t → t < T → x ∈ D.boundary →
        D.normalDeriv (u t) x = 0 ∧ D.normalDeriv (v t) x = 0) :
    IsPaper2ClassicalSolution D p T u v :=
  ⟨hT, hreg, hpos, hpde_u, hpde_v, hneumann⟩

lemma IsPaper2GlobalClassicalSolution.of_classical
    {D : BoundedDomainData} {p : CM2Params}
    {u v : ℝ → D.Point → ℝ}
    (h : ∀ T > 0, IsPaper2ClassicalSolution D p T u v) :
    IsPaper2GlobalClassicalSolution D p u v :=
  h

lemma IsPaper2ClassicalSolution.T_pos
    {D : BoundedDomainData} {p : CM2Params} {T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : IsPaper2ClassicalSolution D p T u v) :
    0 < T :=
  h.1

lemma IsPaper2ClassicalSolution.regularity
    {D : BoundedDomainData} {p : CM2Params} {T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : IsPaper2ClassicalSolution D p T u v) :
    D.classicalRegularity T u v :=
  h.2.1

lemma IsPaper2ClassicalSolution.u_pos
    {D : BoundedDomainData} {p : CM2Params} {T t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2ClassicalSolution D p T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ D.inside) :
    0 < u t x :=
  h.2.2.1 t x ht0 htT hx

lemma IsPaper2ClassicalSolution.pde_u
    {D : BoundedDomainData} {p : CM2Params} {T t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2ClassicalSolution D p T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ D.inside) :
    D.timeDeriv u t x =
      D.laplacian (u t) x
        - p.χ₀ * D.chemotaxisDiv p (u t) (v t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α) :=
  h.2.2.2.1 t x ht0 htT hx

lemma IsPaper2ClassicalSolution.pde_v
    {D : BoundedDomainData} {p : CM2Params} {T t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2ClassicalSolution D p T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ D.inside) :
    0 = D.laplacian (v t) x - p.μ * v t x + p.ν * (u t x) ^ p.γ :=
  h.2.2.2.2.1 t x ht0 htT hx

lemma IsPaper2ClassicalSolution.neumann
    {D : BoundedDomainData} {p : CM2Params} {T t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2ClassicalSolution D p T u v)
    (ht0 : 0 < t) (htT : t < T) (hx : x ∈ D.boundary) :
    D.normalDeriv (u t) x = 0 ∧ D.normalDeriv (v t) x = 0 :=
  h.2.2.2.2.2 t x ht0 htT hx

lemma IsPaper2GlobalClassicalSolution.classical
    {D : BoundedDomainData} {p : CM2Params} {T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : IsPaper2GlobalClassicalSolution D p u v) (hT : 0 < T) :
    IsPaper2ClassicalSolution D p T u v :=
  h T hT

lemma IsPaper2GlobalClassicalSolution.regularity
    {D : BoundedDomainData} {p : CM2Params} {T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : IsPaper2GlobalClassicalSolution D p u v) (hT : 0 < T) :
    D.classicalRegularity T u v :=
  (h.classical hT).regularity

lemma IsPaper2GlobalClassicalSolution.u_pos
    {D : BoundedDomainData} {p : CM2Params} {t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2GlobalClassicalSolution D p u v)
    (ht0 : 0 < t) (hx : x ∈ D.inside) :
    0 < u t x := by
  have hT : 0 < t + 1 := by linarith
  exact (h.classical hT).u_pos ht0 (by linarith) hx

lemma IsPaper2GlobalClassicalSolution.pde_u
    {D : BoundedDomainData} {p : CM2Params} {t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2GlobalClassicalSolution D p u v)
    (ht0 : 0 < t) (hx : x ∈ D.inside) :
    D.timeDeriv u t x =
      D.laplacian (u t) x
        - p.χ₀ * D.chemotaxisDiv p (u t) (v t) x
        + u t x * (p.a - p.b * (u t x) ^ p.α) := by
  have hT : 0 < t + 1 := by linarith
  exact (h.classical hT).pde_u ht0 (by linarith) hx

lemma IsPaper2GlobalClassicalSolution.pde_v
    {D : BoundedDomainData} {p : CM2Params} {t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2GlobalClassicalSolution D p u v)
    (ht0 : 0 < t) (hx : x ∈ D.inside) :
    0 = D.laplacian (v t) x - p.μ * v t x + p.ν * (u t x) ^ p.γ := by
  have hT : 0 < t + 1 := by linarith
  exact (h.classical hT).pde_v ht0 (by linarith) hx

lemma IsPaper2GlobalClassicalSolution.neumann
    {D : BoundedDomainData} {p : CM2Params} {t : ℝ}
    {u v : ℝ → D.Point → ℝ} {x : D.Point}
    (h : IsPaper2GlobalClassicalSolution D p u v)
    (ht0 : 0 < t) (hx : x ∈ D.boundary) :
    D.normalDeriv (u t) x = 0 ∧ D.normalDeriv (v t) x = 0 := by
  have hT : 0 < t + 1 := by linarith
  exact (h.classical hT).neumann ht0 (by linarith) hx

def InitialTrace
    (D : BoundedDomainData) (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    D.supNorm (fun x => u t x - u₀ x) < ε

lemma InitialTrace.eventually_small
    {D : BoundedDomainData} {u₀ : D.Point → ℝ} {u : ℝ → D.Point → ℝ}
    (h : InitialTrace D u₀ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      D.supNorm (fun x => u t x - u₀ x) < ε :=
  h ε hε

def PositiveInitialDatum (D : BoundedDomainData) (u₀ : D.Point → ℝ) : Prop :=
  D.initialAdmissible u₀ ∧ ∀ x, x ∈ D.inside → 0 < u₀ x

lemma PositiveInitialDatum.admissible
    {D : BoundedDomainData} {u₀ : D.Point → ℝ}
    (h : PositiveInitialDatum D u₀) :
    D.initialAdmissible u₀ :=
  h.1

lemma PositiveInitialDatum.pos
    {D : BoundedDomainData} {u₀ : D.Point → ℝ}
    (h : PositiveInitialDatum D u₀) {x : D.Point} (hx : x ∈ D.inside) :
    0 < u₀ x :=
  h.2 x hx

def IsPaper2Bounded (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ M, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M

lemma IsPaper2Bounded.eventually_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    (h : IsPaper2Bounded D u) :
    ∃ M, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M :=
  h

lemma IsPaper2Bounded.of_eventually_supNorm_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {M : ℝ}
    (h : ∀ᶠ t in atTop, D.supNorm (u t) ≤ M) :
    IsPaper2Bounded D u :=
  ⟨M, h⟩

lemma IsPaper2Bounded.of_forall_ge_supNorm_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T M : ℝ}
    (h : ∀ t, T ≤ t → D.supNorm (u t) ≤ M) :
    IsPaper2Bounded D u := by
  exact ⟨M, eventually_atTop.mpr ⟨T, h⟩⟩

lemma IsPaper2Bounded.of_forall_nonneg_supNorm_le
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {M : ℝ}
    (h : ∀ t, 0 ≤ t → D.supNorm (u t) ≤ M) :
    IsPaper2Bounded D u :=
  IsPaper2Bounded.of_forall_ge_supNorm_le (T := 0) h

def IsPaper2BoundedBefore
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ M, ∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ M

lemma IsPaper2BoundedBefore.uniform_bound
    {D : BoundedDomainData} {Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : IsPaper2BoundedBefore D Tmax u) :
    ∃ M, ∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ M :=
  h

lemma IsPaper2BoundedBefore.bound
    {D : BoundedDomainData} {Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : IsPaper2BoundedBefore D Tmax u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    ∃ M, D.supNorm (u t) ≤ M := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, hM t ht0 htT⟩

def LpPowerBoundedBefore
    (D : BoundedDomainData) (pExp Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ C, ∀ t, 0 < t → t < Tmax →
    D.integral (fun x => (u t x) ^ pExp) ≤ C

lemma LpPowerBoundedBefore.uniform_bound
    {D : BoundedDomainData} {pExp Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : LpPowerBoundedBefore D pExp Tmax u) :
    ∃ C, ∀ t, 0 < t → t < Tmax →
      D.integral (fun x => (u t x) ^ pExp) ≤ C :=
  h

lemma LpPowerBoundedBefore.bound
    {D : BoundedDomainData} {pExp Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : LpPowerBoundedBefore D pExp Tmax u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    ∃ C, D.integral (fun x => (u t x) ^ pExp) ≤ C := by
  rcases h with ⟨C, hC⟩
  exact ⟨C, hC t ht0 htT⟩

def MassConservedBefore
    (D : BoundedDomainData) (Tmax : ℝ)
    (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < Tmax → D.integral (u t) = D.integral u₀

lemma MassConservedBefore.eq
    {D : BoundedDomainData} {Tmax : ℝ}
    {u₀ : D.Point → ℝ} {u : ℝ → D.Point → ℝ}
    (h : MassConservedBefore D Tmax u₀ u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    D.integral (u t) = D.integral u₀ :=
  h t ht0 htT

def LogisticMassUpperBoundBefore
    (D : BoundedDomainData) (p : CM2Params) (Tmax : ℝ)
    (u₀ : D.Point → ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < Tmax →
    D.integral (u t) ≤
      max (D.integral u₀) (((p.a / p.b) ^ (1 / p.α)) * D.volume)

lemma LogisticMassUpperBoundBefore.bound
    {D : BoundedDomainData} {p : CM2Params} {Tmax : ℝ}
    {u₀ : D.Point → ℝ} {u : ℝ → D.Point → ℝ}
    (h : LogisticMassUpperBoundBefore D p Tmax u₀ u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < Tmax) :
    D.integral (u t) ≤
      max (D.integral u₀) (((p.a / p.b) ^ (1 / p.α)) * D.volume) :=
  h t ht0 htT

def SupNormNonincreasingOn
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ) (I : Set ℝ) : Prop :=
  ∀ t₁, t₁ ∈ I → ∀ t₂, t₂ ∈ I → t₁ ≤ t₂ →
    D.supNorm (u t₂) ≤ D.supNorm (u t₁)

lemma SupNormNonincreasingOn.bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {I : Set ℝ}
    (h : SupNormNonincreasingOn D u I)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ I) (ht₂ : t₂ ∈ I) (ht : t₁ ≤ t₂) :
    D.supNorm (u t₂) ≤ D.supNorm (u t₁) :=
  h t₁ ht₁ t₂ ht₂ ht

/-- Constant-in-time profiles have nonincreasing abstract sup norm on every
time set.  This is the unconditional branch of the Lemma 3.1 conclusion that
does not use the fakeable PDE fields. -/
lemma SupNormNonincreasingOn.of_forall_eq
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {I : Set ℝ}
    {w : D.Point → ℝ} (hconst : ∀ t, t ∈ I → u t = w) :
    SupNormNonincreasingOn D u I := by
  intro t₁ ht₁ t₂ ht₂ _ht
  rw [hconst t₂ ht₂, hconst t₁ ht₁]

/-! ### Concrete interval semigroup bridges

These theorems expose the audit-passing interval operator from
`PDE/IntervalDomain.lean` at the Paper2 statement layer.  They are not
projections from `SemigroupEstimateData`; the proofs call the concrete kernel
estimates for the restricted reflected heat operator on `[0,L]`.
-/

/-- The restricted interval helper kernel has mass at most one. -/
theorem intervalSemigroupOperator_paper2_kernel_mass_le_one
    {L t : ℝ} (ht : 0 < t) :
    ∀ x : ℝ,
      ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
        ∂ ShenWork.IntervalDomain.intervalMeasure L ≤ 1 := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_intervalIntegral_le_one
    ht L x

/-- The restricted interval helper kernel has nonnegative mass. -/
theorem intervalSemigroupOperator_paper2_kernel_mass_nonneg
    {L t : ℝ} (ht : 0 < t) :
    ∀ x : ℝ,
      0 ≤
        ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
          ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.normalizedZerothReflectionKernel_intervalIntegral_nonneg
    ht L x

/-- Concrete interval semigroup `L¹ → L∞` smoothing for interval-integrable
inputs. -/
theorem intervalSemigroupOperator_paper2_L1_Linfty
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_int :
      MeasureTheory.Integrable f
        (ShenWork.IntervalDomain.intervalMeasure L)) :
    ∀ x : ℝ,
      ‖ShenWork.IntervalDomain.intervalSemigroupOperator L t f x‖ ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y, ‖f y‖ ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_L1_Linfty
    ht hf_int x

/-- Absolute-value form of the concrete interval semigroup `L¹ → L∞`
smoothing estimate. -/
theorem intervalSemigroupOperator_paper2_L1_Linfty_abs
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_int :
      MeasureTheory.Integrable f
        (ShenWork.IntervalDomain.intervalMeasure L)) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y, |f y| ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_L1_Linfty_abs
    ht hf_int x

/-- Concrete interval semigroup trap invariance for bounded nonnegative
inputs. -/
theorem intervalSemigroupOperator_paper2_trap_bound
    {L t Mf M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_le : ∀ y, f y ≤ M) :
    ∀ x : ℝ,
      0 ≤ ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ∧
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ≤ M := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_interval_bound_bounded
    ht hM hf_meas hf_bound hf_nonneg hf_le x

/-- Concrete interval semigroup `L¹ → L∞` smoothing with the interval length
made explicit for bounded inputs. -/
theorem intervalSemigroupOperator_paper2_length_smoothing
    {L t M : ℝ} (hL : 0 ≤ L) (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ M) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) * (M * L) := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_L1_Linfty_abs_le_length
    hL ht hf_meas hf_bound x

/-- Concrete interval semigroup `L∞` bound for bounded inputs. -/
theorem intervalSemigroupOperator_paper2_Linfty_bound
    {L t Mf M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_abs : ∀ y, |f y| ≤ M) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x| ≤ M := by
  have _ : MeasureTheory.Integrable f
      (ShenWork.IntervalDomain.intervalMeasure L) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hf_meas hf_bound
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_Linfty_bound
    ht hM hf_abs x

/-- Concrete interval semigroup `L∞` contraction for bounded input pairs. -/
theorem intervalSemigroupOperator_paper2_contraction
    {L t Mf Mg M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f g : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, |f y - g y| ≤ M) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x| ≤ M := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_contraction_bounded
    ht hM hf_meas hg_meas hf_bound hg_bound hfg x

/-- Concrete interval semigroup additivity for bounded input pairs. -/
theorem intervalSemigroupOperator_paper2_add
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => f y + g y) x =
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x +
          ShenWork.IntervalDomain.intervalSemigroupOperator L t g x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_add_bounded
    ht hf_meas hg_meas hf_bound hg_bound x

/-- Concrete interval semigroup sends zero input to zero. -/
theorem intervalSemigroupOperator_paper2_zero
    (L t : ℝ) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
        (fun _ => (0 : ℝ)) x = 0 := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_zero L t x

/-- Concrete interval semigroup scalar multiplication for bounded inputs. -/
theorem intervalSemigroupOperator_paper2_const_mul
    {L t Mf : ℝ} (a : ℝ)
    {f : ℝ → ℝ}
    (_hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (_hf_bound : ∀ y, |f y| ≤ Mf) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => a * f y) x =
        a * ShenWork.IntervalDomain.intervalSemigroupOperator L t f x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_const_mul a L t f x

/-- Concrete interval semigroup subtraction for bounded input pairs. -/
theorem intervalSemigroupOperator_paper2_sub
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => f y - g y) x =
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
          ShenWork.IntervalDomain.intervalSemigroupOperator L t g x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_sub_bounded
    ht hf_meas hg_meas hf_bound hg_bound x

/-- Concrete interval semigroup monotonicity for bounded input pairs. -/
theorem intervalSemigroupOperator_paper2_mono
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, f y ≤ g y) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ≤
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_mono_bounded
    ht hf_meas hg_meas hf_bound hg_bound hfg x

/-- Concrete interval semigroup sharp kernel-mass interval bound. -/
theorem intervalSemigroupOperator_paper2_kernel_mass_interval_bound
    {L t Mf a b : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_ge : ∀ y, a ≤ f y) (hf_le : ∀ y, f y ≤ b) :
    ∀ x : ℝ,
      a *
          ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
            ∂ ShenWork.IntervalDomain.intervalMeasure L ≤
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ∧
      ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ≤
        b *
          ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
            ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_kernel_mass_interval_bound_bounded
    ht hf_meas hf_bound hf_ge hf_le x

/-- Concrete interval semigroup signed interval bound when the input is
bounded between constants of opposite sign. -/
theorem intervalSemigroupOperator_paper2_signed_interval_bound
    {L t Mf a b : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (hf_ge : ∀ y, a ≤ f y) (hf_le : ∀ y, f y ≤ b) :
    ∀ x : ℝ,
      a ≤ ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ∧
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ≤ b := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_signed_interval_bound_bounded
    ht hf_meas hf_bound ha hb hf_ge hf_le x

/-- Concrete domination by applying the interval semigroup to the pointwise
absolute value. -/
theorem intervalSemigroupOperator_paper2_abs_le_operator_abs
    {L t Mf : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x| ≤
        ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => |f y|) x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_abs_le_operator_abs_bounded
    ht hf_meas hf_bound x

/-- Concrete interval semigroup contraction on constant inputs. -/
theorem intervalSemigroupOperator_paper2_const_contraction
    {t : ℝ} (ht : 0 < t) (L c d : ℝ) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t (fun _ => c) x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t (fun _ => d) x| ≤
        |c - d| := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_const_contraction
    ht L c d x

/-- Concrete interval semigroup difference `L¹ → L∞` smoothing for bounded
input pairs. -/
theorem intervalSemigroupOperator_paper2_diff_L1_Linfty
    {L t Mf Mg : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y, |f y - g y| ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_diff_L1_Linfty_abs_bounded
    ht hf_meas hg_meas hf_bound hg_bound x

/-- Concrete interval semigroup additivity for interval-integrable inputs. -/
theorem intervalSemigroupOperator_paper2_add_integrable
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int :
      MeasureTheory.Integrable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_int :
      MeasureTheory.Integrable g
        (ShenWork.IntervalDomain.intervalMeasure L)) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => f y + g y) x =
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x +
          ShenWork.IntervalDomain.intervalSemigroupOperator L t g x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_add ht
    hf_int hg_int x

/-- Concrete interval semigroup subtraction for interval-integrable inputs. -/
theorem intervalSemigroupOperator_paper2_sub_integrable
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int :
      MeasureTheory.Integrable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_int :
      MeasureTheory.Integrable g
        (ShenWork.IntervalDomain.intervalMeasure L)) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => f y - g y) x =
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
          ShenWork.IntervalDomain.intervalSemigroupOperator L t g x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_sub ht
    hf_int hg_int x

/-- Concrete interval semigroup monotonicity for interval-integrable inputs. -/
theorem intervalSemigroupOperator_paper2_mono_integrable
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int :
      MeasureTheory.Integrable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_int :
      MeasureTheory.Integrable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hfg : ∀ y, f y ≤ g y) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ≤
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_mono ht
    hf_int hg_int hfg x

/-- Concrete interval semigroup `L∞` contraction for interval-integrable
input pairs. -/
theorem intervalSemigroupOperator_paper2_contraction_integrable
    {L t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f g : ℝ → ℝ}
    (hf_int :
      MeasureTheory.Integrable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_int :
      MeasureTheory.Integrable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hfg : ∀ y, |f y - g y| ≤ M) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x| ≤ M := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_contraction
    ht hM hf_int hg_int hfg x

/-- Concrete interval semigroup difference `L¹ → L∞` smoothing for
interval-integrable input pairs. -/
theorem intervalSemigroupOperator_paper2_diff_L1_Linfty_integrable
    {L t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_int :
      MeasureTheory.Integrable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_int :
      MeasureTheory.Integrable g
        (ShenWork.IntervalDomain.intervalMeasure L)) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y, |f y - g y| ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_diff_L1_Linfty_abs
    ht hf_int hg_int x

/-- Concrete interval semigroup pairwise contraction with the restricted
kernel mass kept explicit. -/
theorem intervalSemigroupOperator_paper2_contraction_kernel_mass
    {L t Mf Mg M : ℝ} (ht : 0 < t)
    {f g : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, |f y - g y| ≤ M) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x| ≤
        M *
          ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
            ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_contraction_kernel_mass_bounded
    ht hf_meas hg_meas hf_bound hg_bound hfg x

/-- Concrete interval semigroup symmetric contraction interval for bounded
input pairs. -/
theorem intervalSemigroupOperator_paper2_contraction_symmetric_interval_bound
    {L t Mf Mg M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f g : ℝ → ℝ}
    (hf_meas :
      MeasureTheory.AEStronglyMeasurable f
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, |f y - g y| ≤ M) :
    ∀ x : ℝ,
      -M ≤
          ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
            ShenWork.IntervalDomain.intervalSemigroupOperator L t g x ∧
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
            ShenWork.IntervalDomain.intervalSemigroupOperator L t g x ≤ M := by
  intro x
  exact
    ShenWork.IntervalDomain.intervalSemigroupOperator_contraction_symmetric_interval_bound_bounded
      ht hM hf_meas hg_meas hf_bound hg_bound hfg x

/-- Concrete interval semigroup absolute bound for constant inputs. -/
theorem intervalSemigroupOperator_paper2_const_abs_le
    {t : ℝ} (ht : 0 < t) (L c : ℝ) :
    ∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t (fun _ => c) x| ≤
        |c| := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_const_abs_le ht x

theorem intervalSemigroupOperator_paper2_nonneg
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, 0 ≤ f y) :
    ∀ x : ℝ,
      0 ≤ ShenWork.IntervalDomain.intervalSemigroupOperator L t f x := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_nonneg ht hf x

theorem intervalSemigroupOperator_paper2_const
    (L t c : ℝ) :
    ∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t (fun _ => c) x =
        c * ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
            ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_const_eq_kernel_mass_mul L t c x

theorem intervalSemigroupOperator_paper2_one_interval
    {L t : ℝ} (ht : 0 < t) :
    ∀ x : ℝ,
      0 ≤ ShenWork.IntervalDomain.intervalSemigroupOperator L t (fun _ => 1) x ∧
        ShenWork.IntervalDomain.intervalSemigroupOperator L t (fun _ => 1) x ≤ 1 := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_one_interval ht x

theorem intervalSemigroupOperator_paper2_submarkov
    {L t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M Mf : ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_nonneg : ∀ y, 0 ≤ f y) (hf_le : ∀ y, f y ≤ M) :
    ∀ x : ℝ,
      0 ≤ ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ∧
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ≤
          M * ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
              ∂ ShenWork.IntervalDomain.intervalMeasure L := by
  intro x
  exact ShenWork.IntervalDomain.intervalSemigroupOperator_submarkov_interval_bound_bounded
    ht hf_meas hf_bound hf_nonneg hf_le x

/-- Consolidated concrete interval semigroup estimates for a bounded
nonnegative input.  This is the statement-layer bridge that should be used
instead of a `SemigroupEstimateData` projection when only the interval helper
operator estimates are needed. -/
theorem intervalSemigroupOperator_paper2_basic_bounds
    {L t Mf M : ℝ} (hL : 0 ≤ L) (ht : 0 < t) (hM : 0 ≤ M)
    {f : ℝ → ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hf_abs : ∀ y, |f y| ≤ M)
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_le : ∀ y, f y ≤ M) :
    (∀ x : ℝ,
      ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
        ∂ ShenWork.IntervalDomain.intervalMeasure L ≤ 1) ∧
    (∀ x : ℝ,
      0 ≤
        ∫ y, ShenWork.IntervalDomain.normalizedZerothReflectionKernel L t x y
          ∂ ShenWork.IntervalDomain.intervalMeasure L) ∧
    (∀ x : ℝ,
      ‖ShenWork.IntervalDomain.intervalSemigroupOperator L t f x‖ ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y, ‖f y‖ ∂ ShenWork.IntervalDomain.intervalMeasure L) ∧
    (∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x| ≤ M) ∧
    (∀ x : ℝ,
      0 ≤ ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ∧
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x ≤ M) ∧
    (∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) * (M * L)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact intervalSemigroupOperator_paper2_kernel_mass_le_one ht
  · exact intervalSemigroupOperator_paper2_kernel_mass_nonneg ht
  · exact intervalSemigroupOperator_paper2_L1_Linfty ht
      (ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
        hf_meas hf_bound)
  · exact intervalSemigroupOperator_paper2_Linfty_bound
      ht hM hf_meas hf_bound hf_abs
  · exact intervalSemigroupOperator_paper2_trap_bound
      ht hM hf_meas hf_bound hf_nonneg hf_le
  · exact intervalSemigroupOperator_paper2_length_smoothing
      hL ht hf_meas hf_abs

/-- Consolidated concrete interval semigroup estimates for a bounded input
pair.  The conclusion records linearity, `L∞` contraction, and the
`L¹ → L∞` difference smoothing estimate without using `SemigroupEstimateData`.
-/
theorem intervalSemigroupOperator_paper2_pair_bounds
    {L t Mf Mg M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    {f g : ℝ → ℝ}
    (hf_meas : MeasureTheory.AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure L))
    (hg_meas : MeasureTheory.AEStronglyMeasurable g
      (ShenWork.IntervalDomain.intervalMeasure L))
    (hf_bound : ∀ y, |f y| ≤ Mf)
    (hg_bound : ∀ y, |g y| ≤ Mg)
    (hfg : ∀ y, |f y - g y| ≤ M) :
    (∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x| ≤ M) ∧
    (∀ x : ℝ,
      |ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
        ShenWork.IntervalDomain.intervalSemigroupOperator L t g x| ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y, |f y - g y| ∂ ShenWork.IntervalDomain.intervalMeasure L) ∧
    (∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => f y + g y) x =
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x +
          ShenWork.IntervalDomain.intervalSemigroupOperator L t g x) ∧
    (∀ x : ℝ,
      ShenWork.IntervalDomain.intervalSemigroupOperator L t
          (fun y => f y - g y) x =
        ShenWork.IntervalDomain.intervalSemigroupOperator L t f x -
          ShenWork.IntervalDomain.intervalSemigroupOperator L t g x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact intervalSemigroupOperator_paper2_contraction
      ht hM hf_meas hg_meas hf_bound hg_bound hfg
  · exact intervalSemigroupOperator_paper2_diff_L1_Linfty
      ht hf_meas hg_meas hf_bound hg_bound
  · exact intervalSemigroupOperator_paper2_add
      ht hf_meas hg_meas hf_bound hg_bound
  · exact intervalSemigroupOperator_paper2_sub
      ht hf_meas hg_meas hf_bound hg_bound

def WeightedGradientEstimate
    (D : BoundedDomainData) (pExp beta gamma Mstar T : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T →
    D.integral
        (fun x => (D.gradNorm (v t) x) ^ (2 * pExp) / (v t x) ^ pExp) ≤
      Mstar * D.integral (fun x => (u t x) ^ (gamma * pExp)) ∧
    D.integral
        (fun x =>
          (D.gradNorm (v t) x) ^ (2 * pExp) /
            (1 + v t x) ^ ((1 + beta) * pExp)) ≤
      (Theta_beta beta) ^ pExp * Mstar *
        D.integral (fun x => (u t x) ^ (gamma * pExp))

def WeightedSignalEstimate
    (D : BoundedDomainData) (pExp beta gamma eps Ceps T : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T →
    D.integral (fun x => (v t x) ^ (pExp + 1) / (1 + v t x) ^ beta) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (gamma * (pExp + 1)) / (1 + v t x) ^ beta) +
        Ceps *
          (D.integral
            (fun x => v t x / (1 + v t x) ^ (beta / (pExp + 1)))) ^ (pExp + 1)

lemma WeightedGradientEstimate.first
    {D : BoundedDomainData} {pExp beta gamma Mstar T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : WeightedGradientEstimate D pExp beta gamma Mstar T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral
        (fun x => (D.gradNorm (v t) x) ^ (2 * pExp) / (v t x) ^ pExp) ≤
      Mstar * D.integral (fun x => (u t x) ^ (gamma * pExp)) :=
  (h t ht0 htT).1

lemma WeightedGradientEstimate.second
    {D : BoundedDomainData} {pExp beta gamma Mstar T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : WeightedGradientEstimate D pExp beta gamma Mstar T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral
        (fun x =>
          (D.gradNorm (v t) x) ^ (2 * pExp) /
            (1 + v t x) ^ ((1 + beta) * pExp)) ≤
      (Theta_beta beta) ^ pExp * Mstar *
        D.integral (fun x => (u t x) ^ (gamma * pExp)) :=
  (h t ht0 htT).2

lemma WeightedSignalEstimate.bound
    {D : BoundedDomainData} {pExp beta gamma eps Ceps T : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : WeightedSignalEstimate D pExp beta gamma eps Ceps T u v)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral (fun x => (v t x) ^ (pExp + 1) / (1 + v t x) ^ beta) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (gamma * (pExp + 1)) / (1 + v t x) ^ beta) +
        Ceps *
          (D.integral
            (fun x => v t x / (1 + v t x) ^ (beta / (pExp + 1)))) ^ (pExp + 1) :=
  h t ht0 htT

def LpBootstrapEnergyInequality
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ pExp, p0 ≤ pExp →
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      ∀ t, 0 < t → t < T →
        (1 / pExp) *
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
          A *
            D.integral
              (fun x =>
                (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ pExp) ≤
        K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L

lemma LpBootstrapEnergyInequality.constants
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T rho p0 : ℝ}
    (h : LpBootstrapEnergyInequality D u T rho p0)
    {pExp : ℝ} (hpExp : p0 ≤ pExp) :
    ∃ A > 0, ∃ B > 0, ∃ K > 0, ∃ L,
      ∀ t, 0 < t → t < T →
        (1 / pExp) *
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
          A *
            D.integral
              (fun x =>
                (D.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
          B * D.integral (fun x => (u t x) ^ pExp) ≤
        K * D.integral (fun x => (u t x) ^ (pExp + rho)) + L :=
  h pExp hpExp

def CrossDiffusionBootstrapEstimate
    (D : BoundedDomainData) (p : CM2Params) (T rho : ℝ)
    (u v : ℝ → D.Point → ℝ) : Prop :=
  ∀ eps > 0, ∀ pExp > 1, ∃ Ceps,
    ∀ t, 0 < t → t < T →
      D.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        eps *
            D.integral
              (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ (pExp + rho))

def LpMassGradientInterpolationEstimate
    (D : BoundedDomainData) (pExp eps Ceps T : ℝ)
    (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ t, 0 < t → t < T →
    D.integral (fun x => (u t x) ^ pExp) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
        Ceps * (D.integral (u t)) ^ pExp

lemma LpMassGradientInterpolationEstimate.bound
    {D : BoundedDomainData} {pExp eps Ceps T : ℝ}
    {u : ℝ → D.Point → ℝ}
    (h : LpMassGradientInterpolationEstimate D pExp eps Ceps T u)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    D.integral (fun x => (u t x) ^ pExp) ≤
      eps *
          D.integral
            (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
        Ceps * (D.integral (u t)) ^ pExp :=
  h t ht0 htT

lemma CrossDiffusionBootstrapEstimate.bound
    {D : BoundedDomainData} {p : CM2Params} {T rho : ℝ}
    {u v : ℝ → D.Point → ℝ}
    (h : CrossDiffusionBootstrapEstimate D p T rho u v)
    {eps pExp t : ℝ} (heps : 0 < eps) (hpExp : 1 < pExp)
    (ht0 : 0 < t) (htT : t < T) :
    ∃ Ceps,
      D.crossDiffusionEnergyTerm p pExp (u t) (v t) ≤
        eps *
            D.integral
              (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
          Ceps * D.integral (fun x => (u t x) ^ (pExp + rho)) := by
  rcases h eps heps pExp hpExp with ⟨Ceps, hCeps⟩
  exact ⟨Ceps, hCeps t ht0 htT⟩

def FiniteHorizonAlternative
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  (∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x) ∨
    (∀ δ > 0, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ u t x < δ)

lemma FiniteHorizonAlternative.unbounded_or_vanishes
    {D : BoundedDomainData} {Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : FiniteHorizonAlternative D Tmax u) :
    (∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x) ∨
      (∀ δ > 0, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ u t x < δ) :=
  h

def MGeOneFiniteHorizonAlternative
    (D : BoundedDomainData) (Tmax : ℝ) (u : ℝ → D.Point → ℝ) : Prop :=
  ∀ M, ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x

lemma MGeOneFiniteHorizonAlternative.apply
    {D : BoundedDomainData} {Tmax : ℝ} {u : ℝ → D.Point → ℝ}
    (h : MGeOneFiniteHorizonAlternative D Tmax u) (M : ℝ) :
    ∃ t x, 0 < t ∧ t < Tmax ∧ x ∈ D.inside ∧ M < u t x :=
  h M

def chiBeta (p : CM2Params) : ℝ :=
  2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))

lemma chiBeta_denom_pos (p : CM2Params) :
    0 < max (2 : ℝ) (p.γ * (p.N : ℝ)) :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

lemma chiBeta_pos_of_one_le_beta (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < chiBeta p := by
  unfold chiBeta
  have hnum : 0 < 2 * (2 * p.β - 1) := by nlinarith
  exact div_pos hnum (chiBeta_denom_pos p)

lemma chiBeta_half_pos_of_one_le_beta (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < chiBeta p / 2 := by
  exact half_pos (chiBeta_pos_of_one_le_beta p hβ)

lemma sqrt_chiBeta_pos_of_one_le_beta (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < Real.sqrt (chiBeta p) := by
  exact Real.sqrt_pos.mpr (chiBeta_pos_of_one_le_beta p hβ)

lemma min_chiBeta_half_sqrt_pos_of_one_le_beta
    (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < min (chiBeta p / 2) (Real.sqrt (chiBeta p)) :=
  lt_min
    (chiBeta_half_pos_of_one_le_beta p hβ)
    (sqrt_chiBeta_pos_of_one_le_beta p hβ)

lemma lt_chiBeta_of_lt_min_half_sqrt
    (p : CM2Params) {chi : ℝ} (hβ : 1 ≤ p.β)
    (hchi : chi < min (chiBeta p / 2) (Real.sqrt (chiBeta p))) :
    chi < chiBeta p := by
  have hhalf : chi < chiBeta p / 2 := lt_of_lt_of_le hchi (min_le_left _ _)
  have hpos : 0 < chiBeta p := chiBeta_pos_of_one_le_beta p hβ
  nlinarith

lemma chiBeta_nonneg_of_half_le_beta (p : CM2Params) (hβ : (1 / 2 : ℝ) ≤ p.β) :
    0 ≤ chiBeta p := by
  unfold chiBeta
  apply div_nonneg
  · nlinarith
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)

lemma chiBeta_pos_of_half_lt_beta (p : CM2Params) (hβ : (1 / 2 : ℝ) < p.β) :
    0 < chiBeta p := by
  unfold chiBeta
  apply div_pos
  · nlinarith
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

lemma chiBeta_le_two_beta_sub_one (p : CM2Params) (hβ : (1 / 2 : ℝ) ≤ p.β) :
    chiBeta p ≤ 2 * p.β - 1 := by
  unfold chiBeta
  have hnum_nonneg : 0 ≤ 2 * (2 * p.β - 1) := by nlinarith
  have hden_ge_two : (2 : ℝ) ≤ max 2 (p.γ * (p.N : ℝ)) := le_max_left _ _
  have hden_pos : 0 < max (2 : ℝ) (p.γ * (p.N : ℝ)) :=
    lt_of_lt_of_le (by norm_num) hden_ge_two
  have hmul :
      2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ)) ≤
        2 * (2 * p.β - 1) / 2 := by
    exact div_le_div_of_nonneg_left hnum_nonneg (by norm_num) hden_ge_two
  nlinarith

lemma chiBeta_eq_two_beta_sub_one_of_gamma_mul_N_le_two
    (p : CM2Params) (hden : p.γ * (p.N : ℝ) ≤ 2) :
    chiBeta p = 2 * p.β - 1 := by
  unfold chiBeta
  rw [max_eq_left hden]
  ring

lemma chiBeta_lt_two_beta_sub_one_of_two_lt_denom
    (p : CM2Params) (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < max 2 (p.γ * (p.N : ℝ))) :
    chiBeta p < 2 * p.β - 1 := by
  unfold chiBeta
  have hnum_pos : 0 < 2 * (2 * p.β - 1) := by nlinarith
  calc
    2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))
        < 2 * (2 * p.β - 1) / 2 := by
          exact div_lt_div_of_pos_left hnum_pos (by norm_num) hden
    _ = 2 * p.β - 1 := by ring

lemma chiBeta_lt_of_lt_two_beta_sub_one
    (p : CM2Params) {chi : ℝ} (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < max 2 (p.γ * (p.N : ℝ)))
    (hchi : chi < chiBeta p) :
    chi < 2 * p.β - 1 :=
  lt_trans hchi (chiBeta_lt_two_beta_sub_one_of_two_lt_denom p hβ hden)

lemma chiBeta_lt_two_beta_sub_one_of_two_lt_gamma_mul_N
    (p : CM2Params) (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < p.γ * (p.N : ℝ)) :
    chiBeta p < 2 * p.β - 1 :=
  chiBeta_lt_two_beta_sub_one_of_two_lt_denom p hβ
    (by rwa [max_eq_right hden.le])

lemma chiBeta_lt_of_lt_two_beta_sub_one_gamma_mul_N
    (p : CM2Params) {chi : ℝ} (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < p.γ * (p.N : ℝ))
    (hchi : chi < chiBeta p) :
    chi < 2 * p.β - 1 :=
  lt_trans hchi (chiBeta_lt_two_beta_sub_one_of_two_lt_gamma_mul_N p hβ hden)

structure SemigroupEstimateData (D : BoundedDomainData) where
  lpNorm : ℝ → (D.Point → ℝ) → ℝ
  vectorLpNorm : ℝ → (D.Point → ℝ) → ℝ
  fractionalNorm : ℝ → ℝ → (D.Point → ℝ) → ℝ
  semigroup : ℝ → (D.Point → ℝ) → D.Point → ℝ
  divergenceSemigroup : ℝ → (D.Point → ℝ) → D.Point → ℝ
  embeddingNorm : ℝ → ℝ → ℝ → (D.Point → ℝ) → ℝ

def Lemma_2_1 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  (∀ sigma q delta, 0 ≤ sigma → 1 ≤ q → 0 < delta → delta < p.μ →
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.fractionalNorm sigma q (S.semigroup t u) ≤
        C * t ^ (-sigma) * Real.exp (-delta * t) * S.lpNorm q u) ∧
  (∀ sigma, 0 < sigma → sigma ≤ 1 →
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.lpNorm 2 (fun x => S.semigroup t u x - u x) ≤
        C * t ^ sigma * S.fractionalNorm sigma 2 u)

theorem Lemma_2_1_zero_output_branch
    (D : BoundedDomainData) (p : CM2Params) (S : SemigroupEstimateData D)
    (hlp_nonneg : ∀ q u, 0 ≤ S.lpNorm q u)
    (hfrac_nonneg : ∀ sigma q u, 0 ≤ S.fractionalNorm sigma q u)
    (hfrac_semigroup_zero :
      ∀ sigma q t u, S.fractionalNorm sigma q (S.semigroup t u) = 0)
    (hlp_difference_zero :
      ∀ t u, S.lpNorm 2 (fun x => S.semigroup t u x - u x) = 0) :
    Lemma_2_1 D p S := by
  refine ⟨?_, ?_⟩
  · intro sigma q delta _hsigma _hq _hdelta_pos _hdelta_mu
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    have hright_nonneg :
        0 ≤
          (1 : ℝ) * t ^ (-sigma) * Real.exp (-delta * t) * S.lpNorm q u := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
          (Real.exp_nonneg _))
        (hlp_nonneg q u)
    simpa [hfrac_semigroup_zero sigma q t u] using hright_nonneg
  · intro sigma _hsigma_pos _hsigma_one
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    have hright_nonneg :
        0 ≤ (1 : ℝ) * t ^ sigma * S.fractionalNorm sigma 2 u := by
      exact mul_nonneg
        (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
        (hfrac_nonneg sigma 2 u)
    simpa [hlp_difference_zero t u] using hright_nonneg

def Lemma_2_2 (D : BoundedDomainData) (S : SemigroupEstimateData D) : Prop :=
  (∀ sigma q k r, 0 ≤ sigma → 1 ≤ q → q ≤ r →
    k - (D.volume / r) < 2 * sigma - D.volume / q →
      ∃ C > 0, ∀ u : D.Point → ℝ,
        S.embeddingNorm k r sigma u ≤ C * S.fractionalNorm sigma q u) ∧
  (∀ sigma q theta, 0 ≤ theta → theta < 2 * sigma - D.volume / q →
      ∃ C > 0, ∀ u : D.Point → ℝ,
        S.embeddingNorm theta q sigma u ≤ C * S.fractionalNorm sigma q u)

theorem Lemma_2_2_zero_embedding_branch
    (D : BoundedDomainData) (S : SemigroupEstimateData D)
    (hfrac_nonneg : ∀ sigma q u, 0 ≤ S.fractionalNorm sigma q u)
    (hembed_general_zero : ∀ k r sigma u, S.embeddingNorm k r sigma u = 0)
    (hembed_same_zero : ∀ theta q sigma u, S.embeddingNorm theta q sigma u = 0) :
    Lemma_2_2 D S := by
  refine ⟨?_, ?_⟩
  · intro sigma q k r _hsigma _hq _hqr _hcond
    refine ⟨1, zero_lt_one, ?_⟩
    intro u
    have hright_nonneg : 0 ≤ (1 : ℝ) * S.fractionalNorm sigma q u := by
      exact mul_nonneg zero_le_one (hfrac_nonneg sigma q u)
    simpa [hembed_general_zero k r sigma u] using hright_nonneg
  · intro sigma q theta _htheta_nonneg _hcond
    refine ⟨1, zero_lt_one, ?_⟩
    intro u
    have hright_nonneg : 0 ≤ (1 : ℝ) * S.fractionalNorm sigma q u := by
      exact mul_nonneg zero_le_one (hfrac_nonneg sigma q u)
    simpa [hembed_same_zero theta q sigma u] using hright_nonneg

def Lemma_2_3 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ phi : D.Point → ℝ,
    S.lpNorm q (S.divergenceSemigroup t phi) ≤
      C * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(p.μ) * t) * S.vectorLpNorm q phi

theorem Lemma_2_3_zero_divergence_branch
    (D : BoundedDomainData) (p : CM2Params) (S : SemigroupEstimateData D)
    (hvector_nonneg : ∀ q phi, 0 ≤ S.vectorLpNorm q phi)
    (hlp_div_zero : ∀ q t phi, S.lpNorm q (S.divergenceSemigroup t phi) = 0) :
    Lemma_2_3 D p S := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro q _hq t ht phi
  have hfactor_nonneg : 0 ≤ 1 + t ^ (-(1 / 2 : ℝ)) := by
    have hpow : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    linarith
  have hright_nonneg :
      0 ≤
        (1 : ℝ) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-p.μ * t) * S.vectorLpNorm q phi := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg zero_le_one hfactor_nonneg)
        (Real.exp_nonneg _))
      (hvector_nonneg q phi)
  simpa [hlp_div_zero q t phi] using hright_nonneg

def Lemma_2_4 (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∀ sigma q, 0 < sigma → 1 < q →
    ∃ C > 0, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.fractionalNorm sigma q (S.divergenceSemigroup t phi) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ / 2) * t) * S.vectorLpNorm q phi

theorem Lemma_2_4_zero_fractional_divergence_branch
    (D : BoundedDomainData) (p : CM2Params) (S : SemigroupEstimateData D)
    (hvector_nonneg : ∀ q phi, 0 ≤ S.vectorLpNorm q phi)
    (hfrac_div_zero :
      ∀ sigma q t phi,
        S.fractionalNorm sigma q (S.divergenceSemigroup t phi) = 0) :
    Lemma_2_4 D p S := by
  intro sigma q _hsigma _hq
  refine ⟨1, zero_lt_one, ?_⟩
  intro t ht phi
  have hfactor_nonneg : 0 ≤ 1 + t ^ (-(1 / 2 : ℝ)) := by
    have hpow : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
    linarith
  have hright_nonneg :
      0 ≤
        (1 : ℝ) * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ / 2) * t) * S.vectorLpNorm q phi := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _))
          hfactor_nonneg)
        (Real.exp_nonneg _))
      (hvector_nonneg q phi)
  simpa [hfrac_div_zero sigma q t phi] using hright_nonneg

/-- The all-zero semigroup/norm interface.  It is analytically degenerate, but
it is a concrete `SemigroupEstimateData` value whose estimates are proved
directly, not projected from an external package. -/
def zeroSemigroupEstimateData (D : BoundedDomainData) : SemigroupEstimateData D where
  lpNorm := fun _ _ => 0
  vectorLpNorm := fun _ _ => 0
  fractionalNorm := fun _ _ _ => 0
  semigroup := fun _ _ _ => 0
  divergenceSemigroup := fun _ _ _ => 0
  embeddingNorm := fun _ _ _ _ => 0

theorem Lemma_2_1_zero_data (D : BoundedDomainData) (p : CM2Params) :
    Lemma_2_1 D p (zeroSemigroupEstimateData D) := by
  apply Lemma_2_1_zero_output_branch
  · intro q u
    norm_num [zeroSemigroupEstimateData]
  · intro sigma q u
    norm_num [zeroSemigroupEstimateData]
  · intro sigma q t u
    norm_num [zeroSemigroupEstimateData]
  · intro t u
    norm_num [zeroSemigroupEstimateData]

theorem Lemma_2_2_zero_data (D : BoundedDomainData) :
    Lemma_2_2 D (zeroSemigroupEstimateData D) := by
  apply Lemma_2_2_zero_embedding_branch
  · intro sigma q u
    norm_num [zeroSemigroupEstimateData]
  · intro k r sigma u
    norm_num [zeroSemigroupEstimateData]
  · intro theta q sigma u
    norm_num [zeroSemigroupEstimateData]

theorem Lemma_2_3_zero_data (D : BoundedDomainData) (p : CM2Params) :
    Lemma_2_3 D p (zeroSemigroupEstimateData D) := by
  apply Lemma_2_3_zero_divergence_branch
  · intro q phi
    norm_num [zeroSemigroupEstimateData]
  · intro q t phi
    norm_num [zeroSemigroupEstimateData]

theorem Lemma_2_4_zero_data (D : BoundedDomainData) (p : CM2Params) :
    Lemma_2_4 D p (zeroSemigroupEstimateData D) := by
  apply Lemma_2_4_zero_fractional_divergence_branch
  · intro q phi
    norm_num [zeroSemigroupEstimateData]
  · intro sigma q t phi
    norm_num [zeroSemigroupEstimateData]

lemma Psi_beta_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < Psi_beta beta := by
  unfold Psi_beta
  positivity

lemma Psi_beta_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ Psi_beta beta := by
  unfold Psi_beta
  positivity

lemma Psi_beta_zero :
    Psi_beta 0 = 0 := by
  norm_num [Psi_beta]

lemma beta_div_one_add_beta_hasDerivAt {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt (fun b : ℝ => b / (1 + b)) (1 / (1 + beta) ^ 2) beta := by
  have hden : 1 + beta ≠ 0 := by linarith
  have hden_deriv : HasDerivAt (fun b : ℝ => 1 + b) 1 beta := by
    simpa using ((hasDerivAt_const beta (1 : ℝ)).add (hasDerivAt_id beta))
  have hraw :
      HasDerivAt (fun b : ℝ => b / (1 + b))
        ((1 * (1 + beta) - beta * 1) / (1 + beta) ^ 2) beta := by
    simpa using (hasDerivAt_id beta).div hden_deriv hden
  convert hraw using 1
  field_simp [hden]
  ring_nf

lemma Psi_beta_hasDerivAt_raw {beta : ℝ} (hbeta : 0 < beta) :
    HasDerivAt Psi_beta
      ((1 / (1 + beta) ^ 2) * (1 + beta) *
          (beta / (1 + beta)) ^ ((1 + beta) - 1) +
        1 * (beta / (1 + beta)) ^ (1 + beta) *
          Real.log (beta / (1 + beta)))
      beta := by
  have hbase : 0 < beta / (1 + beta) := by positivity
  have hexp_deriv : HasDerivAt (fun b : ℝ => 1 + b) 1 beta := by
    simpa using ((hasDerivAt_const beta (1 : ℝ)).add (hasDerivAt_id beta))
  unfold Psi_beta
  exact (beta_div_one_add_beta_hasDerivAt hbeta).rpow
    hexp_deriv hbase

lemma Psi_beta_deriv_raw {beta : ℝ} (hbeta : 0 < beta) :
    deriv Psi_beta beta =
      (1 / (1 + beta) ^ 2) * (1 + beta) *
          (beta / (1 + beta)) ^ ((1 + beta) - 1) +
        1 * (beta / (1 + beta)) ^ (1 + beta) *
          Real.log (beta / (1 + beta)) :=
  (Psi_beta_hasDerivAt_raw hbeta).deriv

lemma Psi_beta_deriv_eq {beta : ℝ} (hbeta : 0 < beta) :
    deriv Psi_beta beta =
      Psi_beta beta * (1 / beta + Real.log (beta / (1 + beta))) := by
  have hden_pos : 0 < 1 + beta := by linarith
  have hq_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hpow :
      (beta / (1 + beta)) ^ ((1 + beta) - 1) =
        (beta / (1 + beta)) ^ (1 + beta) / (beta / (1 + beta)) := by
    simpa using Real.rpow_sub hq_pos (1 + beta) 1
  rw [Psi_beta_deriv_raw hbeta]
  unfold Psi_beta
  rw [hpow]
  field_simp [ne_of_gt hbeta, ne_of_gt hden_pos, ne_of_gt hq_pos]

lemma Psi_beta_log_factor_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < 1 / beta + Real.log (beta / (1 + beta)) := by
  have hx_pos : 0 < 1 + 1 / beta := by positivity
  have hx_ne : 1 + 1 / beta ≠ 1 := by
    intro h
    have hinv_pos : 0 < 1 / beta := by positivity
    linarith
  have hlog_lt := Real.log_lt_sub_one_of_pos hx_pos hx_ne
  have hquot : beta / (1 + beta) = (1 + 1 / beta)⁻¹ := by
    field_simp [ne_of_gt hbeta, ne_of_gt (by linarith : 0 < 1 + beta)]
    ring
  rw [hquot, Real.log_inv]
  linarith

lemma Psi_beta_deriv_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < deriv Psi_beta beta := by
  rw [Psi_beta_deriv_eq hbeta]
  exact mul_pos (Psi_beta_pos hbeta) (Psi_beta_log_factor_pos hbeta)

lemma Psi_beta_strictMonoOn_Ioi :
    StrictMonoOn Psi_beta (Set.Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) ?_ ?_
  · intro beta hbeta
    exact (Psi_beta_hasDerivAt_raw hbeta).continuousAt.continuousWithinAt
  · intro beta hbeta
    exact Psi_beta_deriv_pos (by simpa using hbeta)

lemma Psi_beta_monotoneOn_Ici :
    MonotoneOn Psi_beta (Set.Ici (0 : ℝ)) := by
  intro beta hbeta gamma hgamma hle
  by_cases hbeta_zero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
    exact Psi_beta_nonneg hgamma
  · have hbeta_pos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hbeta_zero)
    by_cases h_eq : beta = gamma
    · subst gamma
      rfl
    · have hlt : beta < gamma := lt_of_le_of_ne hle h_eq
      have hgamma_pos : 0 < gamma := lt_trans hbeta_pos hlt
      exact le_of_lt (Psi_beta_strictMonoOn_Ioi hbeta_pos hgamma_pos hlt)

lemma Psi_beta_eq_zero_iff_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta = 0 ↔ beta = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hne)
    have := Psi_beta_pos hpos
    linarith
  · intro h
    subst beta
    exact Psi_beta_zero

lemma Psi_beta_pos_iff_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 < Psi_beta beta ↔ 0 < beta := by
  constructor
  · intro h
    exact lt_of_le_of_ne hbeta
      (fun hzero => by
        subst beta
        rw [Psi_beta_zero] at h
        exact (lt_irrefl (0 : ℝ)) h)
  · exact Psi_beta_pos

lemma Psi_beta_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta < 1 := by
  unfold Psi_beta
  have hbase_nonneg : 0 ≤ beta / (1 + beta) := by positivity
  have hbase_lt : beta / (1 + beta) < 1 := by
    rw [div_lt_one (by positivity : 0 < 1 + beta)]
    linarith
  exact Real.rpow_lt_one hbase_nonneg hbase_lt (by linarith : 0 < 1 + beta)

lemma Psi_beta_lt_self {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta < beta := by
  unfold Psi_beta
  have hden_pos : 0 < 1 + beta := by linarith
  have hbase_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hbase_lt_one : beta / (1 + beta) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  calc
    (beta / (1 + beta)) ^ (1 + beta) < beta / (1 + beta) :=
      Real.rpow_lt_self_of_lt_one hbase_pos hbase_lt_one (by linarith)
    _ < beta := by
      rw [div_lt_iff₀ hden_pos]
      nlinarith

lemma Psi_beta_le_self {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ≤ beta := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
  · exact le_of_lt (Psi_beta_lt_self (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Psi_beta_eq_at_inv {beta : ℝ} (hbeta : 0 < beta) :
    beta * (1 / beta) / (1 + 1 / beta) ^ (1 + beta) = Psi_beta beta := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta
  have hden_pos : 0 < 1 + beta := by linarith
  have hbase :
      1 + 1 / beta = (1 + beta) / beta := by
    field_simp [hbeta_ne]
    ring
  have hquot :
      (1 + beta) / beta = (beta / (1 + beta))⁻¹ := by
    field_simp [hbeta_ne, ne_of_gt hden_pos]
  have hfrac_nonneg : 0 ≤ beta / (1 + beta) :=
    div_nonneg hbeta.le hden_pos.le
  unfold Psi_beta
  rw [show beta * (1 / beta) = 1 by field_simp [hbeta_ne]]
  rw [hbase, hquot, Real.inv_rpow hfrac_nonneg]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (div_pos hbeta hden_pos) (1 + beta))]

lemma Psi_beta_le_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ≤ 1 := by
  by_cases hzero : beta = 0
  · subst beta
    norm_num [Psi_beta]
  · exact le_of_lt (Psi_beta_lt_one (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Psi_beta_mem_Icc_zero_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Psi_beta_nonneg hbeta, Psi_beta_le_one hbeta⟩

lemma one_add_inv_tendsto_one_atTop :
    Tendsto (fun beta : ℝ => 1 + 1 / beta) atTop (𝓝 1) := by
  have hinv : Tendsto (fun beta : ℝ => 1 / beta) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  simpa using tendsto_const_nhds.add hinv

lemma one_add_inv_rpow_one_add_tendsto_exp :
    Tendsto (fun beta : ℝ => (1 + 1 / beta) ^ (1 + beta)) atTop
      (𝓝 (Real.exp 1)) := by
  have hp : Tendsto (fun beta : ℝ => (1 + 1 / beta) ^ beta) atTop
      (𝓝 (Real.exp 1)) := by
    simpa [one_div] using Real.tendsto_one_add_div_rpow_exp 1
  have hbase : Tendsto (fun beta : ℝ => 1 + 1 / beta) atTop (𝓝 1) :=
    one_add_inv_tendsto_one_atTop
  have heq :
      (fun beta : ℝ => (1 + 1 / beta) ^ beta * (1 + 1 / beta)) =ᶠ[atTop]
        fun beta : ℝ => (1 + 1 / beta) ^ (1 + beta) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with beta hbeta
    have hbase_pos : 0 < 1 + 1 / beta := by positivity
    rw [show 1 + beta = beta + 1 by ring]
    rw [Real.rpow_add hbase_pos]
    rw [Real.rpow_one]
  simpa using (hp.mul hbase).congr' heq

lemma Psi_beta_tendsto_atTop :
    Tendsto Psi_beta atTop (𝓝 (Real.exp (-1))) := by
  have hlim :
      Tendsto (fun beta : ℝ => ((1 + 1 / beta) ^ (1 + beta))⁻¹)
        atTop (𝓝 ((Real.exp 1)⁻¹)) :=
    one_add_inv_rpow_one_add_tendsto_exp.inv₀ (by positivity)
  have heq :
      (fun beta : ℝ => Psi_beta beta) =ᶠ[atTop]
        fun beta : ℝ => ((1 + 1 / beta) ^ (1 + beta))⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with beta hbeta
    have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta
    have hbase_nonneg : 0 ≤ 1 + 1 / beta := by positivity
    have hquot : beta / (1 + beta) = (1 + 1 / beta)⁻¹ := by
      field_simp [hbeta_ne, ne_of_gt (by linarith : 0 < 1 + beta)]
      ring
    unfold Psi_beta
    rw [hquot, Real.inv_rpow hbase_nonneg]
  have hinv_exp : (Real.exp 1)⁻¹ = Real.exp (-1) := by
    rw [← Real.exp_neg]
  simpa [hinv_exp] using hlim.congr' heq.symm

lemma Psi_beta_tendsto_atRight_zero :
    Tendsto Psi_beta (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine squeeze_zero' (f := Psi_beta) (g := fun beta : ℝ => beta) ?_ ?_ ?_
  · exact eventually_nhdsWithin_of_forall fun beta hbeta =>
      Psi_beta_nonneg (le_of_lt hbeta)
  · exact eventually_nhdsWithin_of_forall fun beta hbeta =>
      Psi_beta_le_self (le_of_lt hbeta)
  · exact
      (tendsto_id :
        Tendsto (fun beta : ℝ => beta) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).mono_left
        nhdsWithin_le_nhds

lemma Psi_beta_le_exp_neg_one {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta ≤ Real.exp (-1) := by
  have hden_pos : 0 < 1 + beta := by linarith
  have hq_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hx_pos : 0 < 1 + 1 / beta := by positivity
  have hquot : beta / (1 + beta) = (1 + 1 / beta)⁻¹ := by
    field_simp [ne_of_gt hbeta, ne_of_gt hden_pos]
    ring
  have hxinv :
      (1 + 1 / beta)⁻¹ = beta / (1 + beta) := hquot.symm
  have hlog_lower := Real.one_sub_inv_le_log_of_pos hx_pos
  rw [hxinv] at hlog_lower
  have hunit :
      1 - beta / (1 + beta) = 1 / (1 + beta) := by
    field_simp [ne_of_gt hden_pos]
    ring
  rw [hunit] at hlog_lower
  have hmul :
      1 ≤ (1 + beta) * Real.log (1 + 1 / beta) := by
    have hmul' := mul_le_mul_of_nonneg_left hlog_lower hden_pos.le
    have hone : (1 + beta) * (1 / (1 + beta)) = 1 := by
      field_simp [ne_of_gt hden_pos]
    nlinarith
  have hlog :
      Real.log (Psi_beta beta) ≤ Real.log (Real.exp (-1)) := by
    unfold Psi_beta
    rw [Real.log_rpow hq_pos, hquot, Real.log_inv]
    rw [Real.log_exp]
    nlinarith
  exact (Real.log_le_log_iff (Psi_beta_pos hbeta) (Real.exp_pos _)).mp hlog

lemma Psi_beta_lt_exp_neg_one {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta < Real.exp (-1) := by
  have hden_pos : 0 < 1 + beta := by linarith
  have hq_pos : 0 < beta / (1 + beta) := div_pos hbeta hden_pos
  have hq_ne_one : beta / (1 + beta) ≠ 1 := by
    have hq_lt_one : beta / (1 + beta) < 1 := by
      rw [div_lt_one hden_pos]
      linarith
    exact ne_of_lt hq_lt_one
  have hlog_q_lt : Real.log (beta / (1 + beta)) < beta / (1 + beta) - 1 :=
    Real.log_lt_sub_one_of_pos hq_pos hq_ne_one
  have hunit :
      (1 + beta) * (beta / (1 + beta) - 1) = -1 := by
    field_simp [ne_of_gt hden_pos]
    ring
  have hlog :
      Real.log (Psi_beta beta) < Real.log (Real.exp (-1)) := by
    unfold Psi_beta
    rw [Real.log_rpow hq_pos, Real.log_exp]
    calc
      (1 + beta) * Real.log (beta / (1 + beta))
          < (1 + beta) * (beta / (1 + beta) - 1) :=
            mul_lt_mul_of_pos_left hlog_q_lt hden_pos
      _ = -1 := hunit
  exact (Real.log_lt_log_iff (Psi_beta_pos hbeta) (Real.exp_pos _)).mp hlog

lemma Psi_beta_le_exp_neg_one_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta ≤ Real.exp (-1) := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
    exact (Real.exp_pos _).le
  · exact le_of_lt (Psi_beta_lt_exp_neg_one (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Psi_beta_lt_exp_neg_one_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Psi_beta beta < Real.exp (-1) := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Psi_beta_zero]
    exact Real.exp_pos _
  · exact Psi_beta_lt_exp_neg_one (lt_of_le_of_ne hbeta (Ne.symm hzero))

lemma Theta_beta_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < Theta_beta beta := by
  unfold Theta_beta
  positivity

lemma Theta_beta_zero :
    Theta_beta 0 = 1 := by
  norm_num [Theta_beta]

lemma Theta_beta_pos_of_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 < Theta_beta beta := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Theta_beta_zero]
    norm_num
  · exact Theta_beta_pos (lt_of_le_of_ne hbeta (Ne.symm hzero))

lemma Theta_beta_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ Theta_beta beta := by
  exact (Theta_beta_pos_of_nonneg hbeta).le

lemma Psi_beta_eq_beta_mul_Theta_beta {beta : ℝ} (hbeta : 0 < beta) :
    Psi_beta beta = beta * Theta_beta beta := by
  have hden_pos : 0 < 1 + beta := by linarith
  unfold Psi_beta Theta_beta
  rw [Real.div_rpow hbeta.le hden_pos.le]
  rw [show 1 + beta = beta + 1 by ring]
  rw [Real.rpow_add_one hbeta.ne' beta]
  have hden_nonneg : 0 ≤ beta + 1 := by linarith
  rw [Real.rpow_neg hden_nonneg]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (by linarith : 0 < beta + 1) (beta + 1))]

lemma Theta_beta_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    Theta_beta beta < 1 := by
  have h := Psi_beta_lt_self hbeta
  rw [Psi_beta_eq_beta_mul_Theta_beta hbeta] at h
  rw [← div_self (ne_of_gt hbeta)]
  rw [lt_div_iff₀ hbeta]
  rwa [mul_comm]

lemma Theta_beta_le_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    Theta_beta beta ≤ 1 := by
  by_cases hzero : beta = 0
  · subst beta
    rw [Theta_beta_zero]
  · exact le_of_lt (Theta_beta_lt_one (lt_of_le_of_ne hbeta (Ne.symm hzero)))

lemma Theta_beta_eq_Psi_beta_div {beta : ℝ} (hbeta : 0 < beta) :
    Theta_beta beta = Psi_beta beta / beta := by
  rw [Psi_beta_eq_beta_mul_Theta_beta hbeta]
  field_simp [ne_of_gt hbeta]

lemma beta_mul_Theta_beta_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    beta * Theta_beta beta < 1 := by
  rw [← Psi_beta_eq_beta_mul_Theta_beta hbeta]
  exact Psi_beta_lt_one hbeta

lemma beta_mul_Theta_beta_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < beta * Theta_beta beta := by
  rw [← Psi_beta_eq_beta_mul_Theta_beta hbeta]
  exact Psi_beta_pos hbeta

lemma beta_mul_Theta_beta_le_one {beta : ℝ} (hbeta : 0 < beta) :
    beta * Theta_beta beta ≤ 1 :=
  le_of_lt (beta_mul_Theta_beta_lt_one hbeta)

/-- Direct scalar form of Paper2 Lemma 2.5, without going through the
theorem-shaped `Prop` wrapper. -/
theorem Lemma_2_5_direct
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta := by
  have hden_pos : 0 < 1 + beta := by linarith
  have hvden_pos : 0 < 1 + v := by linarith
  have hweights : 1 / (1 + beta) + beta / (1 + beta) = 1 := by
    field_simp [ne_of_gt hden_pos]
  have hgm :=
    Real.geom_mean_le_arith_mean2_weighted
      (show 0 ≤ 1 / (1 + beta) by positivity)
      (show 0 ≤ beta / (1 + beta) by positivity)
      (mul_nonneg hbeta.le hv.le)
      (show 0 ≤ (1 : ℝ) by norm_num)
      hweights
      (p₁ := beta * v) (p₂ := 1)
  have hgm' :
      (beta * v) ^ (1 / (1 + beta)) ≤ beta * (1 + v) / (1 + beta) := by
    calc
      (beta * v) ^ (1 / (1 + beta))
          ≤ beta / (beta + 1) + (beta + 1)⁻¹ * (beta * v) := by
            simpa [Real.one_rpow, one_div, add_comm] using hgm
      _ = beta * (1 + v) / (1 + beta) := by
            field_simp [ne_of_gt hden_pos]
            ring
  have hpow :=
    Real.rpow_le_rpow
      (Real.rpow_nonneg (mul_nonneg hbeta.le hv.le) _)
      hgm' (show 0 ≤ 1 + beta by linarith)
  have hleft_eq :
      ((beta * v) ^ (1 / (1 + beta))) ^ (1 + beta) = beta * v := by
    rw [← Real.rpow_mul (mul_nonneg hbeta.le hv.le)]
    have hprod : 1 / (1 + beta) * (1 + beta) = 1 := by
      field_simp [ne_of_gt hden_pos]
    rw [hprod, Real.rpow_one]
  have hrhs_eq :
      (beta * (1 + v) / (1 + beta)) ^ (1 + beta) =
        Psi_beta beta * (1 + v) ^ (1 + beta) := by
    have hbase : beta * (1 + v) / (1 + beta) = (beta / (1 + beta)) * (1 + v) := by
      ring
    rw [hbase]
    rw [Real.mul_rpow (div_nonneg hbeta.le hden_pos.le) hvden_pos.le]
    rfl
  have hmain : beta * v ≤ Psi_beta beta * (1 + v) ^ (1 + beta) := by
    rw [hleft_eq, hrhs_eq] at hpow
    exact hpow
  have hden_rpow_pos : 0 < (1 + v) ^ (1 + beta) :=
    Real.rpow_pos_of_pos hvden_pos _
  exact (div_le_iff₀ hden_rpow_pos).mpr hmain

/-- Direct pointwise form of Paper2 Lemma 2.5, using the proved sharp
constant `Psi_beta`. -/
theorem Lemma_2_5_pointwise_bound
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta :=
  Lemma_2_5_direct hbeta hv

/-- The Paper2 Lemma 2.5 bound is attained at `v = 1 / beta`. -/
theorem Lemma_2_5_attained_at_inv
    {beta : ℝ} (hbeta : 0 < beta) :
    beta * (1 / beta) / (1 + 1 / beta) ^ (1 + beta) =
      Psi_beta beta :=
  Psi_beta_eq_at_inv hbeta

/-- Paper2 Lemma 2.5 as a sharp bound: every positive `v` is bounded by
`Psi_beta beta`, and equality is attained by the positive point `1 / beta`. -/
theorem Lemma_2_5_sharp_bound
    {beta : ℝ} (hbeta : 0 < beta) :
    (∀ v > 0, beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta) ∧
      ∃ v > 0, beta * v / (1 + v) ^ (1 + beta) = Psi_beta beta := by
  refine ⟨?_, ?_⟩
  · intro v hv
    exact Lemma_2_5_pointwise_bound hbeta hv
  · refine ⟨1 / beta, div_pos one_pos hbeta, ?_⟩
    exact Lemma_2_5_attained_at_inv hbeta

/-- The constant `Psi_beta beta` is the least constant that can bound the
Lemma 2.5 expression for all positive `v`. -/
theorem Lemma_2_5_sharp_constant_minimal
    {beta C : ℝ} (hbeta : 0 < beta)
    (hC : ∀ v > 0, beta * v / (1 + v) ^ (1 + beta) ≤ C) :
    Psi_beta beta ≤ C := by
  have hinv_pos : 0 < 1 / beta := div_pos one_pos hbeta
  have h := hC (1 / beta) hinv_pos
  rwa [Lemma_2_5_attained_at_inv hbeta] at h

/-- A real constant bounds the Lemma 2.5 expression on `(0,∞)` exactly when
it is at least the sharp constant `Psi_beta beta`. -/
theorem Lemma_2_5_sharp_constant_iff
    {beta C : ℝ} (hbeta : 0 < beta) :
    (∀ v > 0, beta * v / (1 + v) ^ (1 + beta) ≤ C) ↔
      Psi_beta beta ≤ C := by
  constructor
  · exact Lemma_2_5_sharp_constant_minimal hbeta
  · intro hC v hv
    exact le_trans (Lemma_2_5_pointwise_bound hbeta hv) hC

/-- End-to-end form of the full scalar content of Paper2 Lemma 2.5: the
pointwise inequality, equality at `1 / beta`, strict monotonicity of the sharp
constant, and the two endpoint limits. -/
theorem Lemma_2_5_full_statement :
    (∀ beta v : ℝ, 0 < beta → 0 < v →
      beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta) ∧
    (∀ beta : ℝ, 0 < beta →
      beta * (1 / beta) / (1 + 1 / beta) ^ (1 + beta) =
        Psi_beta beta) ∧
    StrictMonoOn Psi_beta (Set.Ioi (0 : ℝ)) ∧
    Tendsto Psi_beta (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto Psi_beta atTop (𝓝 (Real.exp (-1))) := by
  exact ⟨
    (fun beta v hbeta hv => Lemma_2_5_direct hbeta hv),
    fun beta hbeta => Lemma_2_5_attained_at_inv hbeta,
    Psi_beta_strictMonoOn_Ioi, Psi_beta_tendsto_atRight_zero,
    Psi_beta_tendsto_atTop⟩

/-- If `beta ≤ gamma`, the Lemma 2.5 pointwise expression at `beta` is also
bounded by the larger sharp constant `Psi_beta gamma`. -/
theorem Lemma_2_5_pointwise_bound_le_larger_Psi_beta
    {beta gamma v : ℝ} (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hbg : beta ≤ gamma) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta gamma := by
  exact le_trans
    (Lemma_2_5_pointwise_bound hbeta hv)
    (Psi_beta_monotoneOn_Ici hbeta.le hgamma hbg)

/-- Paper2 Lemma 2.5 with the universal numerical bound
`Psi_beta beta < exp (-1)`. -/
theorem Lemma_2_5_pointwise_bound_exp_neg_one
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ≤ Real.exp (-1) := by
  exact le_trans
    (Lemma_2_5_pointwise_bound hbeta hv)
    (Psi_beta_le_exp_neg_one hbeta)

/-- The Lemma 2.5 expression is strictly positive for positive parameters. -/
theorem Lemma_2_5_pointwise_pos
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    0 < beta * v / (1 + v) ^ (1 + beta) := by
  have hden_pos : 0 < (1 + v) ^ (1 + beta) :=
    Real.rpow_pos_of_pos (by linarith : 0 < 1 + v) _
  exact div_pos (mul_pos hbeta hv) hden_pos

/-- The Lemma 2.5 expression is strictly below the universal constant
`exp (-1)`. -/
theorem Lemma_2_5_pointwise_bound_lt_exp_neg_one
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) < Real.exp (-1) := by
  exact lt_of_le_of_lt
    (Lemma_2_5_pointwise_bound hbeta hv)
    (Psi_beta_lt_exp_neg_one hbeta)

/-- Range form of the scalar Lemma 2.5 estimate. -/
theorem Lemma_2_5_pointwise_mem_Ioo_zero_exp_neg_one
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ∈
      Set.Ioo (0 : ℝ) (Real.exp (-1)) :=
  ⟨Lemma_2_5_pointwise_pos hbeta hv,
    Lemma_2_5_pointwise_bound_lt_exp_neg_one hbeta hv⟩

/-- Strict monotonicity of `Psi_beta` upgrades Lemma 2.5 to a strict bound by
any larger sharp constant. -/
theorem Lemma_2_5_pointwise_bound_lt_larger_Psi_beta
    {beta gamma v : ℝ} (hbeta : 0 < beta) (hbg : beta < gamma)
    (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) < Psi_beta gamma := by
  have hgamma : 0 < gamma := lt_trans hbeta hbg
  exact lt_of_le_of_lt
    (Lemma_2_5_pointwise_bound hbeta hv)
    (Psi_beta_strictMonoOn_Ioi hbeta hgamma hbg)

/-- Any constant that bounds the Lemma 2.5 expression on `(0,∞)` is positive. -/
theorem Lemma_2_5_sharp_constant_positive
    {beta C : ℝ} (hbeta : 0 < beta)
    (hC : ∀ v > 0, beta * v / (1 + v) ^ (1 + beta) ≤ C) :
    0 < C := by
  exact lt_of_lt_of_le (Psi_beta_pos hbeta)
    (Lemma_2_5_sharp_constant_minimal hbeta hC)

/-- End-to-end strengthened range statement for Paper2 Lemma 2.5.  It records
the strict universal range, the strict larger-parameter bound coming from
`Psi_beta` monotonicity, and positivity of every admissible sharp constant. -/
theorem Lemma_2_5_full_range_statement :
    (∀ beta v : ℝ, 0 < beta → 0 < v →
      beta * v / (1 + v) ^ (1 + beta) ∈
        Set.Ioo (0 : ℝ) (Real.exp (-1))) ∧
    (∀ beta gamma v : ℝ, 0 < beta → beta < gamma → 0 < v →
      beta * v / (1 + v) ^ (1 + beta) < Psi_beta gamma) ∧
    (∀ beta C : ℝ, 0 < beta →
      (∀ v > 0, beta * v / (1 + v) ^ (1 + beta) ≤ C) →
        0 < C) := by
  exact ⟨
    (fun beta v hbeta hv =>
      Lemma_2_5_pointwise_mem_Ioo_zero_exp_neg_one hbeta hv),
    (fun beta gamma v hbeta hbg hv =>
      Lemma_2_5_pointwise_bound_lt_larger_Psi_beta hbeta hbg hv),
    (fun beta C hbeta hC =>
      Lemma_2_5_sharp_constant_positive hbeta hC)⟩

/-- Paper2 Lemma 2.5 with the coarse bound by `1`. -/
theorem Lemma_2_5_pointwise_bound_one
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ≤ 1 := by
  exact le_trans
    (Lemma_2_5_pointwise_bound hbeta hv)
    (Psi_beta_le_one hbeta.le)

/-- Paper2 Lemma 2.5 with the coarse bound by the parameter `beta`. -/
theorem Lemma_2_5_pointwise_bound_self
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ≤ beta := by
  exact le_trans
    (Lemma_2_5_pointwise_bound hbeta hv)
    (Psi_beta_le_self hbeta.le)

/-- A consolidated end-to-end scalar statement for Paper2 Lemma 2.5.  It ties
the Lemma 2.5 inequality to positivity, the sharp constant characterization,
strict monotonicity of the sharp constants, and the two endpoint limits of
`Psi_beta`. -/
theorem Lemma_2_5_sharp_monotone_range_statement :
    (∀ beta v : ℝ, 0 < beta → 0 < v →
      beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta) ∧
    (∀ beta : ℝ, 0 < beta →
      (0 < Psi_beta beta ∧ Psi_beta beta < Real.exp (-1)) ∧
      (∀ C : ℝ,
        ((∀ v > 0, beta * v / (1 + v) ^ (1 + beta) ≤ C) ↔
          Psi_beta beta ≤ C)) ∧
      ∃ v > 0, beta * v / (1 + v) ^ (1 + beta) = Psi_beta beta) ∧
    StrictMonoOn Psi_beta (Set.Ioi (0 : ℝ)) ∧
    MonotoneOn Psi_beta (Set.Ici (0 : ℝ)) ∧
    Tendsto Psi_beta (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto Psi_beta atTop (𝓝 (Real.exp (-1))) := by
  refine ⟨(fun beta v hbeta hv => Lemma_2_5_direct hbeta hv), ?_,
    Psi_beta_strictMonoOn_Ioi,
    Psi_beta_monotoneOn_Ici, Psi_beta_tendsto_atRight_zero,
    Psi_beta_tendsto_atTop⟩
  intro beta hbeta
  refine ⟨⟨Psi_beta_pos hbeta, Psi_beta_lt_exp_neg_one hbeta⟩, ?_, ?_⟩
  · intro C
    exact Lemma_2_5_sharp_constant_iff hbeta
  · exact (Lemma_2_5_sharp_bound hbeta).2

/-- If the parameter is enlarged, the Lemma 2.5 expression is strictly below
the larger sharp constant, and the sharp constants themselves are strictly
ordered. -/
theorem Lemma_2_5_strict_larger_parameter_statement
    {beta gamma : ℝ} (hbeta : 0 < beta) (hbg : beta < gamma) :
    Psi_beta beta < Psi_beta gamma ∧
      ∀ v > 0,
        beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta ∧
        beta * v / (1 + v) ^ (1 + beta) < Psi_beta gamma := by
  have hgamma : 0 < gamma := lt_trans hbeta hbg
  refine ⟨Psi_beta_strictMonoOn_Ioi hbeta hgamma hbg, ?_⟩
  intro v hv
  exact ⟨Lemma_2_5_pointwise_bound hbeta hv,
    Lemma_2_5_pointwise_bound_lt_larger_Psi_beta hbeta hbg hv⟩

/-- Normalized `Theta_beta` form of Paper2 Lemma 2.5.  This is the same sharp
bound after dividing the Lemma 2.5 expression by the positive parameter
`beta`. -/
theorem Lemma_2_5_normalized_Theta_bound
    {beta v : ℝ} (hbeta : 0 < beta) (hv : 0 < v) :
    v / (1 + v) ^ (1 + beta) ≤ Theta_beta beta := by
  have h :=
    Lemma_2_5_pointwise_bound (beta := beta) (v := v) hbeta hv
  rw [Psi_beta_eq_beta_mul_Theta_beta hbeta] at h
  have hmul :
      beta * (v / (1 + v) ^ (1 + beta)) ≤
        beta * Theta_beta beta := by
    simpa [mul_div_assoc] using h
  exact le_of_mul_le_mul_left hmul hbeta

/-- The normalized `Theta_beta` bound is attained at `v = 1 / beta`. -/
theorem Lemma_2_5_normalized_Theta_attained_at_inv
    {beta : ℝ} (hbeta : 0 < beta) :
    (1 / beta) / (1 + 1 / beta) ^ (1 + beta) =
      Theta_beta beta := by
  have h :=
    Lemma_2_5_attained_at_inv (beta := beta) hbeta
  rw [Psi_beta_eq_beta_mul_Theta_beta hbeta] at h
  have hmul :
      beta * ((1 / beta) / (1 + 1 / beta) ^ (1 + beta)) =
        beta * Theta_beta beta := by
    rwa [mul_div_assoc] at h
  exact mul_left_cancel₀ (ne_of_gt hbeta) hmul

/-- Sharp normalized form of Paper2 Lemma 2.5. -/
theorem Lemma_2_5_normalized_Theta_sharp_bound
    {beta : ℝ} (hbeta : 0 < beta) :
    (∀ v > 0, v / (1 + v) ^ (1 + beta) ≤ Theta_beta beta) ∧
      ∃ v > 0, v / (1 + v) ^ (1 + beta) = Theta_beta beta := by
  refine ⟨?_, ?_⟩
  · intro v hv
    exact Lemma_2_5_normalized_Theta_bound hbeta hv
  · refine ⟨1 / beta, div_pos one_pos hbeta, ?_⟩
    exact Lemma_2_5_normalized_Theta_attained_at_inv hbeta

def AbstractLpBootstrapHypothesis
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (N T rho p0 : ℝ) : Prop :=
  0 < rho ∧
    0 < T ∧
    max 1 (rho * N / 2) < p0 ∧
    LpPowerBoundedBefore D p0 T u

def Lemma_2_6 (D : BoundedDomainData) : Prop :=
  ∀ N > 0, ∀ u : ℝ → D.Point → ℝ, ∀ T rho p0,
    AbstractLpBootstrapHypothesis D u N T rho p0 →
      LpBootstrapEnergyInequality D u T rho p0 →
        ∀ pExp > 1, LpPowerBoundedBefore D pExp T u

lemma AbstractLpBootstrapHypothesis.rho_pos
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    0 < rho :=
  h.1

lemma AbstractLpBootstrapHypothesis.T_pos
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    0 < T :=
  h.2.1

lemma AbstractLpBootstrapHypothesis.p0_gt_threshold
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    max 1 (rho * N / 2) < p0 :=
  h.2.2.1

lemma AbstractLpBootstrapHypothesis.initial_lp_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {N T rho p0 : ℝ}
    (h : AbstractLpBootstrapHypothesis D u N T rho p0) :
    LpPowerBoundedBefore D p0 T u :=
  h.2.2.2

def Corollary_2_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      (∃ rho > 0, CrossDiffusionBootstrapEstimate D p T rho u v ∧
        ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
          LpPowerBoundedBefore D p0 T u) →
      ∀ pExp > 1, LpPowerBoundedBefore D pExp T u

/-- Time scale used in the fake cross-diffusion bootstrap counterexample. -/
def corollary21CounterR (t : ℝ) : ℝ := (1 - t)⁻¹

/-- A two-coordinate positive profile whose square and cube traces are disjoint. -/
def corollary21CounterU (t : ℝ) : Bool → ℝ :=
  fun b => if b then Real.exp ((corollary21CounterR t) ^ 2)
    else Real.exp (corollary21CounterR t)

/-- Fake integral: it vanishes on the square trace but records `r` on the cube trace. -/
def corollary21CounterIntegral (f : Bool → ℝ) : ℝ :=
  if 0 < f false ∧
      f true = Real.exp ((Real.log (f false)) ^ 2 / 2) then
    0
  else if 0 < f false ∧
      f true = Real.exp ((Real.log (f false)) ^ 2 / 3) then
    Real.log (f false) / 3
  else
    0

def corollary21CounterDomain : BoundedDomainData :=
  { Point := Bool
    inside := Set.univ
    boundary := ∅
    volume := 1
    supNorm := fun _ => 0
    infValue := fun _ => 0
    integral := corollary21CounterIntegral
    gradNorm := fun _ _ => 0
    timeDeriv := fun _ _ _ => 0
    laplacian := fun _ _ => 0
    chemotaxisDiv := fun _ _ _ _ => 0
    crossDiffusionEnergyTerm := fun _ _ _ _ => 0
    normalDeriv := fun _ _ => 0
    initialAdmissible := fun _ => True
    classicalRegularity := fun _ _ _ => True }

def corollary21CounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 0
    b := 0
    β := 0
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma corollary21CounterR_pos {t : ℝ} (ht : t < 1) :
    0 < corollary21CounterR t := by
  unfold corollary21CounterR
  exact inv_pos.mpr (sub_pos.mpr ht)

lemma corollary21Counter_exp_rpow_two (r : ℝ) :
    (Real.exp r) ^ (2 : ℝ) = Real.exp (2 * r) := by
  rw [Real.rpow_two]
  rw [pow_two, ← Real.exp_add]
  ring_nf

lemma corollary21Counter_exp_rpow_three (r : ℝ) :
    (Real.exp r) ^ (3 : ℝ) = Real.exp (3 * r) := by
  rw [Real.rpow_ofNat]
  rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
  ring_nf

lemma corollary21CounterIntegral_two {t : ℝ} (ht : t < 1) :
    corollary21CounterDomain.integral
      (fun x => (corollary21CounterU t x) ^ (2 : ℝ)) = 0 := by
  let r := corollary21CounterR t
  have hr : 0 < r := corollary21CounterR_pos ht
  have hfalse :
      (corollary21CounterU t false) ^ (2 : ℝ) = Real.exp (2 * r) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_two r
  have htrue :
      (corollary21CounterU t true) ^ (2 : ℝ) = Real.exp (2 * r ^ 2) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_two (r ^ 2)
  have hcond :
      0 < (corollary21CounterU t false) ^ (2 : ℝ) ∧
        (corollary21CounterU t true) ^ (2 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (2 : ℝ))) ^ 2 / 2) := by
    constructor
    · change 0 < (corollary21CounterU t false) ^ (2 : ℝ)
      rw [hfalse]
      positivity
    · change (corollary21CounterU t true) ^ (2 : ℝ) =
        Real.exp ((Real.log ((corollary21CounterU t false) ^ (2 : ℝ))) ^ 2 / 2)
      rw [hfalse, htrue, Real.log_exp]
      ring_nf
  dsimp [corollary21CounterDomain]
  unfold corollary21CounterIntegral
  change
    (if 0 < (corollary21CounterU t false) ^ (2 : ℝ) ∧
        (corollary21CounterU t true) ^ (2 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (2 : ℝ))) ^ 2 / 2)
      then 0
      else if 0 < (corollary21CounterU t false) ^ (2 : ℝ) ∧
          (corollary21CounterU t true) ^ (2 : ℝ) =
            Real.exp ((Real.log ((corollary21CounterU t false) ^ (2 : ℝ))) ^ 2 / 3)
        then Real.log ((corollary21CounterU t false) ^ (2 : ℝ)) / 3
        else 0) = 0
  rw [if_pos hcond]

lemma corollary21CounterIntegral_three {t : ℝ} (ht : t < 1) :
    corollary21CounterDomain.integral
      (fun x => (corollary21CounterU t x) ^ (3 : ℝ)) =
        corollary21CounterR t := by
  let r := corollary21CounterR t
  have hr : 0 < r := corollary21CounterR_pos ht
  have hfalse :
      (corollary21CounterU t false) ^ (3 : ℝ) = Real.exp (3 * r) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_three r
  have htrue :
      (corollary21CounterU t true) ^ (3 : ℝ) = Real.exp (3 * r ^ 2) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_three (r ^ 2)
  have hcond2 :
      0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
        (corollary21CounterU t true) ^ (3 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 3) := by
    constructor
    · change 0 < (corollary21CounterU t false) ^ (3 : ℝ)
      rw [hfalse]
      positivity
    · change (corollary21CounterU t true) ^ (3 : ℝ) =
        Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 3)
      rw [hfalse, htrue, Real.log_exp]
      ring_nf
  have hnot_cond1 :
      ¬ (0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
        (corollary21CounterU t true) ^ (3 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 2)) := by
    rintro ⟨_, hbad⟩
    rw [hfalse, htrue, Real.log_exp] at hbad
    have hlin : 3 * r ^ 2 = (3 * r) ^ 2 / 2 :=
      Real.exp_injective hbad
    have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr
    have hcontr : (3 : ℝ) * r ^ 2 ≠ (3 * r) ^ 2 / 2 := by
      intro h
      have h' : (3 : ℝ) * r ^ 2 = (9 / 2) * r ^ 2 := by
        calc
          (3 : ℝ) * r ^ 2 = (3 * r) ^ 2 / 2 := h
          _ = (9 / 2) * r ^ 2 := by ring
      have hcoef : (3 : ℝ) = 9 / 2 := by
        exact mul_right_cancel₀ (ne_of_gt hr2_pos) h'
      norm_num at hcoef
    exact hcontr hlin
  have hlog : Real.log ((corollary21CounterU t false) ^ (3 : ℝ)) / 3 = r := by
    rw [hfalse, Real.log_exp]
    ring
  dsimp [corollary21CounterDomain]
  unfold corollary21CounterIntegral
  change
    (if 0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
        (corollary21CounterU t true) ^ (3 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 2)
      then 0
      else if 0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
          (corollary21CounterU t true) ^ (3 : ℝ) =
            Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 3)
        then Real.log ((corollary21CounterU t false) ^ (3 : ℝ)) / 3
        else 0) = corollary21CounterR t
  rw [if_neg hnot_cond1, if_pos hcond2, hlog]

lemma corollary21Counter_solution :
    IsPaper2ClassicalSolution corollary21CounterDomain corollary21CounterParams 1
      corollary21CounterU corollary21CounterU := by
  refine IsPaper2ClassicalSolution.of_components (by norm_num) trivial ?_ ?_ ?_ ?_
  · intro t x _ht0 _htT _hx
    unfold corollary21CounterU
    split <;> positivity
  · intro t x _ht0 _htT _hx
    simp [corollary21CounterDomain, corollary21CounterParams]
  · intro t x _ht0 _htT _hx
    simp [corollary21CounterDomain, corollary21CounterParams, Real.rpow_one]
  · intro t x _ht0 _htT hx
    exfalso
    simpa [corollary21CounterDomain] using hx

lemma corollary21Counter_cross :
    CrossDiffusionBootstrapEstimate corollary21CounterDomain corollary21CounterParams 1 1
      corollary21CounterU corollary21CounterU := by
  intro eps _heps pExp _hpExp
  refine ⟨0, ?_⟩
  intro t _ht0 _htT
  simp [corollary21CounterDomain, corollary21CounterIntegral]

lemma corollary21Counter_lp_two :
    LpPowerBoundedBefore corollary21CounterDomain 2 1 corollary21CounterU := by
  refine ⟨0, ?_⟩
  intro t _ht0 htT
  rw [corollary21CounterIntegral_two htT]

lemma corollary21Counter_not_lp_three :
    ¬ LpPowerBoundedBefore corollary21CounterDomain 3 1 corollary21CounterU := by
  rintro ⟨C, hC⟩
  let R : ℝ := max 2 (C + 1)
  have hR_gt_one : 1 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hR_pos : 0 < R := by linarith
  have hC_lt_R : C < R := by
    have hle : C + 1 ≤ R := le_max_right _ _
    linarith
  let t : ℝ := 1 - R⁻¹
  have ht0 : 0 < t := by
    dsimp [t]
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hR_gt_one
  have ht1 : t < 1 := by
    dsimp [t]
    linarith [inv_pos.mpr hR_pos]
  have hR_eq : corollary21CounterR t = R := by
    dsimp [corollary21CounterR, t]
    rw [sub_sub_cancel, inv_inv]
  have hle := hC t ht0 ht1
  rw [corollary21CounterIntegral_three ht1, hR_eq] at hle
  linarith

lemma not_forall_Corollary_2_1 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Corollary_2_1 D p) := by
  intro h
  have hcor := h corollary21CounterDomain corollary21CounterParams
  have hbound :=
    hcor 1 (by norm_num) corollary21CounterU corollary21CounterU
      corollary21Counter_solution
      ⟨1, by norm_num, corollary21Counter_cross, 2, by norm_num [corollary21CounterParams],
        corollary21Counter_lp_two⟩
      3 (by norm_num)
  exact corollary21Counter_not_lp_three hbound

def lemma26CounterIntegral (f : Bool → ℝ) : ℝ :=
  if 0 < f false ∧
      f true = Real.exp ((Real.log (f false)) ^ 2 / 3) then
    Real.log (f false) / 3
  else
    0

def lemma26CounterDomain : BoundedDomainData :=
  { corollary21CounterDomain with
    integral := lemma26CounterIntegral }

lemma lemma26CounterIntegral_three {t : ℝ} (_ht : t < 1) :
    lemma26CounterDomain.integral
      (fun x => (corollary21CounterU t x) ^ (3 : ℝ)) =
        corollary21CounterR t := by
  let r := corollary21CounterR t
  have hfalse :
      (corollary21CounterU t false) ^ (3 : ℝ) = Real.exp (3 * r) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_three r
  have htrue :
      (corollary21CounterU t true) ^ (3 : ℝ) = Real.exp (3 * r ^ 2) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_three (r ^ 2)
  have hcond :
      0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
        (corollary21CounterU t true) ^ (3 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 3) := by
    constructor
    · rw [hfalse]
      positivity
    · rw [hfalse, htrue, Real.log_exp]
      ring_nf
  have hlog : Real.log ((corollary21CounterU t false) ^ (3 : ℝ)) / 3 = r := by
    rw [hfalse, Real.log_exp]
    ring_nf
  dsimp [lemma26CounterDomain]
  unfold lemma26CounterIntegral
  change
    (if 0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
        (corollary21CounterU t true) ^ (3 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 3)
      then Real.log ((corollary21CounterU t false) ^ (3 : ℝ)) / 3
      else 0) = corollary21CounterR t
  rw [if_pos hcond, hlog]

lemma lemma26CounterIntegral_ge_four_zero
    {pExp t : ℝ} (hp4 : 4 ≤ pExp) (ht : t < 1) :
    lemma26CounterDomain.integral
      (fun x => (corollary21CounterU t x) ^ pExp) = 0 := by
  let r := corollary21CounterR t
  have hr : 0 < r := corollary21CounterR_pos ht
  have hp_pos : 0 < pExp := by linarith
  have hfalse :
      (corollary21CounterU t false) ^ pExp = Real.exp (pExp * r) := by
    calc
      (corollary21CounterU t false) ^ pExp = (Real.exp r) ^ pExp := by
        simp [corollary21CounterU, r]
      _ = Real.exp (r * pExp) := (Real.exp_mul r pExp).symm
      _ = Real.exp (pExp * r) := by ring_nf
  have htrue :
      (corollary21CounterU t true) ^ pExp = Real.exp (pExp * r ^ 2) := by
    calc
      (corollary21CounterU t true) ^ pExp = (Real.exp (r ^ 2)) ^ pExp := by
        simp [corollary21CounterU, r]
      _ = Real.exp (r ^ 2 * pExp) := (Real.exp_mul (r ^ 2) pExp).symm
      _ = Real.exp (pExp * r ^ 2) := by ring_nf
  have hnot :
      ¬ (0 < (corollary21CounterU t false) ^ pExp ∧
        (corollary21CounterU t true) ^ pExp =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ pExp)) ^ 2 / 3)) := by
    rintro ⟨_, hbad⟩
    rw [hfalse, htrue, Real.log_exp] at hbad
    have hlin : pExp * r ^ 2 = (pExp * r) ^ 2 / 3 :=
      Real.exp_injective hbad
    have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr
    have hcoef : pExp = pExp ^ 2 / 3 := by
      have h' : pExp * r ^ 2 = (pExp ^ 2 / 3) * r ^ 2 := by
        calc
          pExp * r ^ 2 = (pExp * r) ^ 2 / 3 := hlin
          _ = (pExp ^ 2 / 3) * r ^ 2 := by ring_nf
      exact mul_right_cancel₀ (ne_of_gt hr2_pos) h'
    nlinarith
  dsimp [lemma26CounterDomain]
  unfold lemma26CounterIntegral
  change
    (if 0 < (corollary21CounterU t false) ^ pExp ∧
        (corollary21CounterU t true) ^ pExp =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ pExp)) ^ 2 / 3)
      then Real.log ((corollary21CounterU t false) ^ pExp) / 3
      else 0) = 0
  rw [if_neg hnot]

lemma lemma26Counter_deriv_ge_four_zero
    {pExp t : ℝ} (hp4 : 4 ≤ pExp) (ht : t < 1) :
    deriv
      (fun τ => lemma26CounterDomain.integral
        (fun x => (corollary21CounterU τ x) ^ pExp)) t = 0 := by
  have heq :
      (fun τ => lemma26CounterDomain.integral
        (fun x => (corollary21CounterU τ x) ^ pExp)) =ᶠ[𝓝 t]
        fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with τ hτ
    exact lemma26CounterIntegral_ge_four_zero hp4 hτ
  exact ((hasDerivAt_const (x := t) (c := (0 : ℝ))).congr_of_eventuallyEq heq).deriv

lemma lemma26Counter_energy :
    LpBootstrapEnergyInequality lemma26CounterDomain corollary21CounterU 1 1 4 := by
  intro pExp hp4
  refine ⟨1, by norm_num, 1, by norm_num, 1, by norm_num, 0, ?_⟩
  intro t _ht0 ht1
  have hp4' : 4 ≤ pExp + 1 := by linarith
  rw [lemma26Counter_deriv_ge_four_zero hp4 ht1,
    lemma26CounterIntegral_ge_four_zero hp4 ht1,
    lemma26CounterIntegral_ge_four_zero hp4' ht1]
  have hgrad :
      lemma26CounterDomain.integral
        (fun x =>
          (lemma26CounterDomain.gradNorm
            (fun y => (corollary21CounterU t y) ^ (pExp / 2)) x) ^ 2) = 0 := by
    change lemma26CounterIntegral (fun _ : Bool => (0 : ℝ) ^ 2) = 0
    simp [lemma26CounterIntegral]
  rw [hgrad]
  norm_num

lemma lemma26Counter_lp_four :
    LpPowerBoundedBefore lemma26CounterDomain 4 1 corollary21CounterU := by
  refine ⟨0, ?_⟩
  intro t _ht0 ht1
  rw [lemma26CounterIntegral_ge_four_zero (le_rfl : (4 : ℝ) ≤ 4) ht1]

lemma lemma26Counter_not_lp_three :
    ¬ LpPowerBoundedBefore lemma26CounterDomain 3 1 corollary21CounterU := by
  rintro ⟨C, hC⟩
  let R : ℝ := max 2 (C + 1)
  have hR_gt_one : 1 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hR_pos : 0 < R := by linarith
  have hC_lt_R : C < R := by
    have hle : C + 1 ≤ R := le_max_right _ _
    linarith
  let t : ℝ := 1 - R⁻¹
  have ht0 : 0 < t := by
    dsimp [t]
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hR_gt_one
  have ht1 : t < 1 := by
    dsimp [t]
    linarith [inv_pos.mpr hR_pos]
  have hR_eq : corollary21CounterR t = R := by
    dsimp [corollary21CounterR, t]
    rw [sub_sub_cancel, inv_inv]
  have hle := hC t ht0 ht1
  rw [lemma26CounterIntegral_three ht1, hR_eq] at hle
  linarith

lemma not_forall_Lemma_2_6 :
    ¬ (∀ D : BoundedDomainData, Lemma_2_6 D) := by
  intro h
  have hbound :=
    h lemma26CounterDomain 1 (by norm_num) corollary21CounterU 1 1 4
      ⟨by norm_num, by norm_num, by norm_num, lemma26Counter_lp_four⟩
      lemma26Counter_energy 3 (by norm_num)
  exact lemma26Counter_not_lp_three hbound

def Proposition_2_1
    (D : BoundedDomainData) (p : CM2Params)
    (S : SemigroupEstimateData D) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp, 1 ≤ pExp →
        ∀ t, 0 < t → t < T →
          S.lpNorm pExp (v t) ≤
            (p.ν / p.μ) * S.lpNorm pExp (fun x => (u t x) ^ p.γ)

/-- A deliberately degenerate bounded-domain instance for showing that
`Proposition_2_1` cannot be derived from the current abstract semigroup API
alone.  The PDE side admits the constant solution `u = 1`, `v = 1/2`, but the
fake `lpNorm` below assigns size `1` to the signal and size `0` to the source. -/
def proposition21CounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => |f ()|
  infValue := fun f => f ()
  integral := fun _ => 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def proposition21CounterParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 1
  γ := 1
  m := 1
  μ := 2
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
  hβ := by norm_num

def proposition21CounterU : ℝ → proposition21CounterDomain.Point → ℝ :=
  fun _ _ => 1

def proposition21CounterV : ℝ → proposition21CounterDomain.Point → ℝ :=
  fun _ _ => 1 / 2

def proposition21CounterLpNorm
    (_pExp : ℝ) (f : proposition21CounterDomain.Point → ℝ) : ℝ :=
  if f () = (1 / 2 : ℝ) then 1 else 0

def proposition21CounterSemigroupData :
    SemigroupEstimateData proposition21CounterDomain where
  lpNorm := proposition21CounterLpNorm
  vectorLpNorm := fun _ _ => 0
  fractionalNorm := fun _ _ _ => 0
  semigroup := fun _ u => u
  divergenceSemigroup := fun _ _ _ => 0
  embeddingNorm := fun _ _ _ _ => 0

lemma proposition21Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution proposition21CounterDomain
      proposition21CounterParams T proposition21CounterU
      proposition21CounterV := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num [proposition21CounterU]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition21CounterParams.χ₀ * 0 +
        1 * (proposition21CounterParams.a -
          proposition21CounterParams.b * (1 : ℝ) ^ proposition21CounterParams.α)
    norm_num [proposition21CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition21CounterParams.μ * (1 / 2 : ℝ) +
        proposition21CounterParams.ν * (1 : ℝ) ^ proposition21CounterParams.γ
    norm_num [proposition21CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma not_forall_Proposition_2_1 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
      ∀ S : SemigroupEstimateData D, Proposition_2_1 D p S) := by
  intro h
  have hprop :=
    h proposition21CounterDomain proposition21CounterParams
      proposition21CounterSemigroupData
  have hbad :=
    hprop 1 (by norm_num) proposition21CounterU proposition21CounterV
      (proposition21Counter_classical 1 (by norm_num))
      1 (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  norm_num [proposition21CounterSemigroupData, proposition21CounterLpNorm,
    proposition21CounterU, proposition21CounterV, proposition21CounterParams] at hbad

def Proposition_2_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp > 1, ∃ Mstar > 0,
        WeightedGradientEstimate D pExp p.β p.γ Mstar T u v

/-- A fake domain showing that the weighted gradient estimate is not a
consequence of the current abstract bounded-domain API.  The PDE equations are
the same harmless constant solution as above, but the abstract integral detects
the particular first weighted-gradient integrand and assigns it mass `1`, while
assigning the source integral mass `0`. -/
def proposition22CounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => |f ()|
  infValue := fun f => f ()
  integral := fun f => if f () = (4 : ℝ) then 1 else 0
  gradNorm := fun _ _ => 1
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def proposition22CounterU : ℝ → proposition22CounterDomain.Point → ℝ :=
  fun _ _ => 1

def proposition22CounterV : ℝ → proposition22CounterDomain.Point → ℝ :=
  fun _ _ => 1 / 2

lemma proposition22Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution proposition22CounterDomain
      proposition21CounterParams T proposition22CounterU
      proposition22CounterV := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num [proposition22CounterU]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition21CounterParams.χ₀ * 0 +
        1 * (proposition21CounterParams.a -
          proposition21CounterParams.b * (1 : ℝ) ^ proposition21CounterParams.α)
    norm_num [proposition21CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition21CounterParams.μ * (1 / 2 : ℝ) +
        proposition21CounterParams.ν * (1 : ℝ) ^ proposition21CounterParams.γ
    norm_num [proposition21CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma not_forall_Proposition_2_2 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Proposition_2_2 D p) := by
  intro h
  have hprop := h proposition22CounterDomain proposition21CounterParams
  rcases hprop 1 (by norm_num) proposition22CounterU proposition22CounterV
      (proposition22Counter_classical 1 (by norm_num))
      2 (by norm_num) with
    ⟨Mstar, _hMstar_pos, hestimate⟩
  have hbad := (hestimate (1 / 2) (by norm_num) (by norm_num)).1
  simp [proposition22CounterDomain, proposition22CounterU,
    proposition22CounterV, proposition21CounterParams] at hbad
  norm_num at hbad

def Proposition_2_3 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      ∀ pExp, max 1 p.β < pExp →
        ∀ eps > 0, ∃ Ceps > 0,
          WeightedSignalEstimate D pExp p.β p.γ eps Ceps T u v

/-- A fake domain showing that the weighted signal estimate is not a consequence
of the current abstract bounded-domain API.  The PDE side is again the constant
solution `u = 1`, `v = 1/2`, but the abstract integral detects only the left
weighted-signal integrand at `p = 2`, `β = 0` and assigns it mass `1`; the two
right-hand integrals are assigned mass `0`. -/
def proposition23CounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => |f ()|
  infValue := fun f => f ()
  integral := fun f => if f () = (1 / 8 : ℝ) then 1 else 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def proposition23CounterU : ℝ → proposition23CounterDomain.Point → ℝ :=
  fun _ _ => 1

def proposition23CounterV : ℝ → proposition23CounterDomain.Point → ℝ :=
  fun _ _ => 1 / 2

lemma proposition23Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution proposition23CounterDomain
      proposition21CounterParams T proposition23CounterU
      proposition23CounterV := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num [proposition23CounterU]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition21CounterParams.χ₀ * 0 +
        1 * (proposition21CounterParams.a -
          proposition21CounterParams.b * (1 : ℝ) ^ proposition21CounterParams.α)
    norm_num [proposition21CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition21CounterParams.μ * (1 / 2 : ℝ) +
        proposition21CounterParams.ν * (1 : ℝ) ^ proposition21CounterParams.γ
    norm_num [proposition21CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma not_forall_Proposition_2_3 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Proposition_2_3 D p) := by
  intro h
  have hprop := h proposition23CounterDomain proposition21CounterParams
  rcases hprop 1 (by norm_num) proposition23CounterU proposition23CounterV
      (proposition23Counter_classical 1 (by norm_num))
      2 (by norm_num [proposition21CounterParams]) 1 (by norm_num) with
    ⟨Ceps, _hCeps_pos, hestimate⟩
  have hbad := hestimate (1 / 2) (by norm_num) (by norm_num)
  simp [proposition23CounterDomain, proposition23CounterU,
    proposition23CounterV, proposition21CounterParams] at hbad
  norm_num at hbad

def Proposition_2_4 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
      InitialTrace D u₀ u →
        (p.a = 0 → p.b = 0 → MassConservedBefore D T u₀ u) ∧
          (0 < p.a → 0 < p.b → LogisticMassUpperBoundBefore D p T u₀ u)

/-- A fake bounded-domain interface showing that Proposition 2.4 is not a
consequence of the abstract API alone.  The PDE admits the constant solution
`u = v = 1`, while the abstract `supNorm` makes the initial trace accept the
different datum `u₀ = 2`; the abstract integral then distinguishes the two and
violates mass conservation in the `a = b = 0` branch. -/
def proposition24CounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun _ => 0
  infValue := fun f => f ()
  integral := fun f => f ()
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def proposition24CounterParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 1
  γ := 1
  m := 1
  μ := 1
  ν := 1
  χ₀ := 0
  a := 0
  b := 0
  β := 0
  hα := by norm_num
  hγ := by norm_num
  hm := by norm_num
  hμ := by norm_num
  hν := by norm_num
  ha := by norm_num
  hb := by norm_num
  hβ := by norm_num

def proposition24CounterU0 : proposition24CounterDomain.Point → ℝ :=
  fun _ => 2

def proposition24CounterU : ℝ → proposition24CounterDomain.Point → ℝ :=
  fun _ _ => 1

def proposition24CounterV : ℝ → proposition24CounterDomain.Point → ℝ :=
  fun _ _ => 1

lemma proposition24Counter_initial :
    PositiveInitialDatum proposition24CounterDomain proposition24CounterU0 := by
  constructor
  · trivial
  · intro x hx
    norm_num [proposition24CounterU0]

lemma proposition24Counter_trace :
    InitialTrace proposition24CounterDomain proposition24CounterU0
      proposition24CounterU := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro t ht0 htδ
  simpa [proposition24CounterDomain] using hε

lemma proposition24Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution proposition24CounterDomain
      proposition24CounterParams T proposition24CounterU proposition24CounterV := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num [proposition24CounterU]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition24CounterParams.χ₀ * 0 +
        1 * (proposition24CounterParams.a -
          proposition24CounterParams.b * (1 : ℝ) ^ proposition24CounterParams.α)
    norm_num [proposition24CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition24CounterParams.μ * 1 +
        proposition24CounterParams.ν * (1 : ℝ) ^ proposition24CounterParams.γ
    norm_num [proposition24CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma not_forall_Proposition_2_4 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Proposition_2_4 D p) := by
  intro h
  have hprop := h proposition24CounterDomain proposition24CounterParams
  have hmass :=
    (hprop proposition24CounterU0 proposition24Counter_initial
      1 (by norm_num) proposition24CounterU proposition24CounterV
      (proposition24Counter_classical 1 (by norm_num))
      proposition24Counter_trace).1 rfl rfl
  have hbad := hmass (1 / 2) (by norm_num) (by norm_num)
  simp [proposition24CounterDomain, proposition24CounterU0,
    proposition24CounterU] at hbad

def Proposition_2_5 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v →
      InitialTrace D u₀ u →
        ∀ pExp,
          max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
            LpPowerBoundedBefore D pExp Tmax u →
              IsPaper2BoundedBefore D Tmax u

/-- A fake bounded-domain interface showing that Proposition 2.5 is not a
consequence of the current abstract API alone.  The fake operators make
`u(t) = v(t) = (1 - t)⁻¹` a classical solution on `(0,1)`, and the fake
integral makes every `Lᵖ` bound trivial.  The fake `supNorm`, however, records
the blow-up of this spatially constant profile as `t → 1`. -/
def proposition25CounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => if 0 ≤ f () ∧ f () < 1 then 0 else f ()
  infValue := fun f => f ()
  integral := fun _ => 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def proposition25CounterU0 : proposition25CounterDomain.Point → ℝ :=
  fun _ => 1

def proposition25CounterU : ℝ → proposition25CounterDomain.Point → ℝ :=
  fun t _ => (1 - t)⁻¹

def proposition25CounterV : ℝ → proposition25CounterDomain.Point → ℝ :=
  fun t _ => (1 - t)⁻¹

lemma proposition25Counter_initial :
    PositiveInitialDatum proposition25CounterDomain proposition25CounterU0 := by
  constructor
  · trivial
  · intro x hx
    norm_num [proposition25CounterU0]

lemma proposition25Counter_trace :
    InitialTrace proposition25CounterDomain proposition25CounterU0
      proposition25CounterU := by
  intro ε hε
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro t ht0 htδ
  have hden : 0 < 1 - t := by linarith
  have hdiff :
      (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp [ne_of_gt hden]
    ring
  have hdiff_nonneg : 0 ≤ (1 - t)⁻¹ - 1 := by
    rw [hdiff]
    exact div_nonneg ht0.le hden.le
  have hdiff_lt_one : (1 - t)⁻¹ - 1 < 1 := by
    rw [hdiff]
    rw [div_lt_iff₀ hden]
    linarith
  simp [proposition25CounterDomain, proposition25CounterU0,
    proposition25CounterU, hdiff_nonneg, hdiff_lt_one, hε]

lemma proposition25Counter_classical (T : ℝ) (hT : T = 1) :
    IsPaper2ClassicalSolution proposition25CounterDomain
      proposition24CounterParams T proposition25CounterU proposition25CounterV := by
  subst T
  refine ⟨by norm_num, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    have hden : 0 < 1 - t := by linarith
    exact inv_pos.mpr hden
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition24CounterParams.χ₀ * 0 +
        (1 - t)⁻¹ * (proposition24CounterParams.a -
          proposition24CounterParams.b *
            ((1 - t)⁻¹) ^ proposition24CounterParams.α)
    norm_num [proposition24CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition24CounterParams.μ * (1 - t)⁻¹ +
        proposition24CounterParams.ν *
          ((1 - t)⁻¹) ^ proposition24CounterParams.γ
    norm_num [proposition24CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma proposition25Counter_lp :
    LpPowerBoundedBefore proposition25CounterDomain 2 1
      proposition25CounterU := by
  refine ⟨0, ?_⟩
  intro t ht0 htT
  simp [proposition25CounterDomain]

lemma not_forall_Proposition_2_5 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Proposition_2_5 D p) := by
  intro h
  have hprop := h proposition25CounterDomain proposition24CounterParams
  have hbounded :=
    hprop proposition25CounterU0 proposition25Counter_initial
      1 (by norm_num) proposition25CounterU proposition25CounterV
      (proposition25Counter_classical 1 rfl) proposition25Counter_trace
      2 (by norm_num [proposition24CounterParams]) proposition25Counter_lp
  rcases hbounded with ⟨M, hM⟩
  let t : ℝ := 1 - (|M| + 2)⁻¹
  have hden_pos : 0 < |M| + 2 := by positivity
  have hden_ne : |M| + 2 ≠ 0 := ne_of_gt hden_pos
  have hden_gt_one : 1 < |M| + 2 := by
    have h_abs : 0 ≤ |M| := abs_nonneg M
    linarith
  have hinv_pos : 0 < (|M| + 2)⁻¹ := inv_pos.mpr hden_pos
  have hinv_lt_one : (|M| + 2)⁻¹ < 1 := by
    rw [inv_lt_one₀ hden_pos]
    exact hden_gt_one
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have ht1 : t < 1 := by
    dsimp [t]
    linarith
  have hle := hM t ht0 ht1
  have hval : proposition25CounterU t () = |M| + 2 := by
    dsimp [proposition25CounterU, t]
    rw [sub_sub_cancel, inv_inv]
  have hnot_small : ¬ (0 ≤ proposition25CounterU t () ∧ proposition25CounterU t () < 1) := by
    rw [hval]
    intro hsmall
    linarith
  have hnot_small_val : ¬ (0 ≤ |M| + 2 ∧ |M| + 2 < 1) := by
    intro hsmall
    linarith
  have hle' : |M| + 2 ≤ M := by
    simpa [proposition25CounterDomain, hnot_small, hnot_small_val, hval] using hle
  have hM_abs : M ≤ |M| := le_abs_self M
  linarith

def Lemma_2_7 (D : BoundedDomainData) : Prop :=
  ∀ u : ℝ → D.Point → ℝ, ∀ T pExp C1 C2 C3 C4 eps alpha,
    0 < T → 1 < pExp →
      0 ≤ C1 → 0 ≤ C2 → 0 ≤ C3 → 0 < C4 →
        0 < eps → eps ≤ alpha →
          (∀ t, 0 < t → t < T →
            deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
                C3 * D.integral (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
              C1 + C2 * D.integral (fun x => (u t x) ^ pExp) -
                C4 * D.integral (fun x => (u t x) ^ (pExp + alpha))) →
            LpPowerBoundedBefore D pExp T u

def lemma27CounterIntegral (f : Bool → ℝ) : ℝ :=
  if 0 < f false ∧
      f true = Real.exp ((Real.log (f false)) ^ 2 / 3) then
    Real.log (f false) / 3
  else if 0 < f false ∧
      f true = Real.exp ((Real.log (f false)) ^ 2 / 4) then
    -((Real.log (f false) / 4) ^ 2)
  else
    0

def lemma27CounterDomain : BoundedDomainData :=
  { corollary21CounterDomain with
    integral := lemma27CounterIntegral }

lemma corollary21Counter_exp_rpow_four (r : ℝ) :
    (Real.exp r) ^ (4 : ℝ) = Real.exp (4 * r) := by
  rw [Real.rpow_ofNat]
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_zero]
  simp only [one_mul]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  ring_nf

lemma lemma27CounterIntegral_three {t : ℝ} (ht : t < 1) :
    lemma27CounterDomain.integral
      (fun x => (corollary21CounterU t x) ^ (3 : ℝ)) =
        corollary21CounterR t := by
  let r := corollary21CounterR t
  have hr : 0 < r := corollary21CounterR_pos ht
  have hfalse :
      (corollary21CounterU t false) ^ (3 : ℝ) = Real.exp (3 * r) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_three r
  have htrue :
      (corollary21CounterU t true) ^ (3 : ℝ) = Real.exp (3 * r ^ 2) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_three (r ^ 2)
  have hcond :
      0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
        (corollary21CounterU t true) ^ (3 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 3) := by
    constructor
    · rw [hfalse]
      positivity
    · rw [hfalse, htrue, Real.log_exp]
      ring_nf
  have hlog : Real.log ((corollary21CounterU t false) ^ (3 : ℝ)) / 3 = r := by
    rw [hfalse, Real.log_exp]
    ring
  dsimp [lemma27CounterDomain]
  unfold lemma27CounterIntegral
  change
    (if 0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
        (corollary21CounterU t true) ^ (3 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 3)
      then Real.log ((corollary21CounterU t false) ^ (3 : ℝ)) / 3
      else if 0 < (corollary21CounterU t false) ^ (3 : ℝ) ∧
          (corollary21CounterU t true) ^ (3 : ℝ) =
            Real.exp ((Real.log ((corollary21CounterU t false) ^ (3 : ℝ))) ^ 2 / 4)
        then -((Real.log ((corollary21CounterU t false) ^ (3 : ℝ)) / 4) ^ 2)
        else 0) = corollary21CounterR t
  rw [if_pos hcond, hlog]

lemma lemma27CounterIntegral_four {t : ℝ} (ht : t < 1) :
    lemma27CounterDomain.integral
      (fun x => (corollary21CounterU t x) ^ (4 : ℝ)) =
        -(corollary21CounterR t) ^ 2 := by
  let r := corollary21CounterR t
  have hr : 0 < r := corollary21CounterR_pos ht
  have hfalse :
      (corollary21CounterU t false) ^ (4 : ℝ) = Real.exp (4 * r) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_four r
  have htrue :
      (corollary21CounterU t true) ^ (4 : ℝ) = Real.exp (4 * r ^ 2) := by
    simpa [corollary21CounterU, r] using corollary21Counter_exp_rpow_four (r ^ 2)
  have hnot_cond3 :
      ¬ (0 < (corollary21CounterU t false) ^ (4 : ℝ) ∧
        (corollary21CounterU t true) ^ (4 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (4 : ℝ))) ^ 2 / 3)) := by
    rintro ⟨_, hbad⟩
    rw [hfalse, htrue, Real.log_exp] at hbad
    have hlin : 4 * r ^ 2 = (4 * r) ^ 2 / 3 :=
      Real.exp_injective hbad
    have hr2_pos : 0 < r ^ 2 := sq_pos_of_pos hr
    have hcontr : (4 : ℝ) * r ^ 2 ≠ (4 * r) ^ 2 / 3 := by
      intro h
      have h' : (4 : ℝ) * r ^ 2 = (16 / 3) * r ^ 2 := by
        calc
          (4 : ℝ) * r ^ 2 = (4 * r) ^ 2 / 3 := h
          _ = (16 / 3) * r ^ 2 := by ring
      have hcoef : (4 : ℝ) = 16 / 3 := by
        exact mul_right_cancel₀ (ne_of_gt hr2_pos) h'
      norm_num at hcoef
    exact hcontr hlin
  have hcond4 :
      0 < (corollary21CounterU t false) ^ (4 : ℝ) ∧
        (corollary21CounterU t true) ^ (4 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (4 : ℝ))) ^ 2 / 4) := by
    constructor
    · rw [hfalse]
      positivity
    · rw [hfalse, htrue, Real.log_exp]
      ring_nf
  have hlog : Real.log ((corollary21CounterU t false) ^ (4 : ℝ)) / 4 = r := by
    rw [hfalse, Real.log_exp]
    ring
  dsimp [lemma27CounterDomain]
  unfold lemma27CounterIntegral
  change
    (if 0 < (corollary21CounterU t false) ^ (4 : ℝ) ∧
        (corollary21CounterU t true) ^ (4 : ℝ) =
          Real.exp ((Real.log ((corollary21CounterU t false) ^ (4 : ℝ))) ^ 2 / 3)
      then Real.log ((corollary21CounterU t false) ^ (4 : ℝ)) / 3
      else if 0 < (corollary21CounterU t false) ^ (4 : ℝ) ∧
          (corollary21CounterU t true) ^ (4 : ℝ) =
            Real.exp ((Real.log ((corollary21CounterU t false) ^ (4 : ℝ))) ^ 2 / 4)
        then -((Real.log ((corollary21CounterU t false) ^ (4 : ℝ)) / 4) ^ 2)
        else 0) = -(corollary21CounterR t) ^ 2
  rw [if_neg hnot_cond3, if_pos hcond4, hlog]

lemma corollary21CounterR_hasDerivAt {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt corollary21CounterR ((corollary21CounterR t) ^ 2) t := by
  have hbase : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub (hasDerivAt_id t)
  have hne : (1 - t) ≠ 0 := by
    intro hzero
    apply ht
    linarith
  have h := hbase.inv hne
  unfold corollary21CounterR
  convert h using 1
  field_simp [hne]

lemma lemma27Counter_deriv_three {t : ℝ} (ht : t < 1) :
    deriv
      (fun τ => lemma27CounterDomain.integral
        (fun x => (corollary21CounterU τ x) ^ (3 : ℝ))) t =
      (corollary21CounterR t) ^ 2 := by
  have ht_ne : t ≠ 1 := by linarith
  have heq :
      (fun τ => lemma27CounterDomain.integral
        (fun x => (corollary21CounterU τ x) ^ (3 : ℝ))) =ᶠ[𝓝 t]
        corollary21CounterR := by
    filter_upwards [Iio_mem_nhds ht] with τ hτ
    exact lemma27CounterIntegral_three hτ
  exact ((corollary21CounterR_hasDerivAt ht_ne).congr_of_eventuallyEq heq).deriv

lemma lemma27Counter_not_lp_three :
    ¬ LpPowerBoundedBefore lemma27CounterDomain 3 1 corollary21CounterU := by
  rintro ⟨C, hC⟩
  let R : ℝ := max 2 (C + 1)
  have hR_gt_one : 1 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hR_pos : 0 < R := by linarith
  have hC_lt_R : C < R := by
    have hle : C + 1 ≤ R := le_max_right _ _
    linarith
  let t : ℝ := 1 - R⁻¹
  have ht0 : 0 < t := by
    dsimp [t]
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hR_gt_one
  have ht1 : t < 1 := by
    dsimp [t]
    linarith [inv_pos.mpr hR_pos]
  have hR_eq : corollary21CounterR t = R := by
    dsimp [corollary21CounterR, t]
    rw [sub_sub_cancel, inv_inv]
  have hle := hC t ht0 ht1
  rw [lemma27CounterIntegral_three ht1, hR_eq] at hle
  linarith

lemma not_forall_Lemma_2_7 :
    ¬ (∀ D : BoundedDomainData, Lemma_2_7 D) := by
  intro h
  have hbound :=
    h lemma27CounterDomain corollary21CounterU 1 3 0 0 0 1 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  · exact lemma27Counter_not_lp_three hbound
  · intro t _ht0 ht1
    rw [show (3 : ℝ) + 1 - 1 = 3 by norm_num,
      show (3 : ℝ) + 1 = 4 by norm_num]
    simp only [zero_mul, add_zero, one_mul]
    rw [lemma27Counter_deriv_three ht1, lemma27CounterIntegral_four ht1]
    ring_nf
    exact le_rfl

def Lemma_3_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 →
    (0 < p.a → 0 < p.b →
      ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p T u v →
          ∀ t₀, 0 < t₀ → t₀ < T →
            (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t₀) →
              SupNormNonincreasingOn D u (Set.Ioc (0 : ℝ) t₀)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p T u v →
          SupNormNonincreasingOn D u (Set.Ioo (0 : ℝ) T))

/-- Direct constant-in-time branch of the first alternative in Paper2 Lemma 3.1.
This proves the monotonicity conclusion from an explicit primitive constancy
hypothesis, without using the fakeable abstract PDE fields. -/
theorem Lemma_3_1_nonminimal_constant_time_branch
    {D : BoundedDomainData} {p : CM2Params}
    {T t₀ : ℝ} {u v : ℝ → D.Point → ℝ} {w : D.Point → ℝ}
    (_hχ : p.χ₀ ≤ 0) (_ha : 0 < p.a) (_hb : 0 < p.b)
    (_hT : 0 < T) (_hsol : IsPaper2ClassicalSolution D p T u v)
    (_ht₀_pos : 0 < t₀) (_ht₀_T : t₀ < T)
    (_hsup : (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t₀))
    (hconst : ∀ t, t ∈ Set.Ioc (0 : ℝ) t₀ → u t = w) :
    SupNormNonincreasingOn D u (Set.Ioc (0 : ℝ) t₀) :=
  SupNormNonincreasingOn.of_forall_eq hconst

/-- Direct constant-in-time branch of the minimal case in Paper2 Lemma 3.1. -/
theorem Lemma_3_1_minimal_constant_time_branch
    {D : BoundedDomainData} {p : CM2Params}
    {T : ℝ} {u v : ℝ → D.Point → ℝ} {w : D.Point → ℝ}
    (_hχ : p.χ₀ ≤ 0) (_ha : p.a = 0) (_hb : p.b = 0)
    (_hT : 0 < T) (_hsol : IsPaper2ClassicalSolution D p T u v)
    (hconst : ∀ t, t ∈ Set.Ioo (0 : ℝ) T → u t = w) :
    SupNormNonincreasingOn D u (Set.Ioo (0 : ℝ) T) :=
  SupNormNonincreasingOn.of_forall_eq hconst

/-- Corrected end-to-end Lemma 3.1 branch: if every solution in the relevant
time interval is explicitly constant in time, then both monotonicity conclusions
of Lemma 3.1 follow.  This does not use the refuted abstract PDE implication. -/
theorem Lemma_3_1_of_time_constant_solution_branches
    {D : BoundedDomainData} {p : CM2Params}
    (hnonminimal :
      ∀ {T t₀ : ℝ} {u v : ℝ → D.Point → ℝ},
        0 < p.a → 0 < p.b → 0 < T →
        IsPaper2ClassicalSolution D p T u v →
        0 < t₀ → t₀ < T →
        (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t₀) →
          ∃ w : D.Point → ℝ,
            ∀ t, t ∈ Set.Ioc (0 : ℝ) t₀ → u t = w)
    (hminimal :
      ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
        p.a = 0 → p.b = 0 → 0 < T →
        IsPaper2ClassicalSolution D p T u v →
          ∃ w : D.Point → ℝ,
            ∀ t, t ∈ Set.Ioo (0 : ℝ) T → u t = w) :
    Lemma_3_1 D p := by
  intro hχ
  constructor
  · intro ha hb T hT u v hsol t₀ ht₀_pos ht₀_T hsup
    obtain ⟨w, hw⟩ :=
      hnonminimal ha hb hT hsol ht₀_pos ht₀_T hsup
    exact Lemma_3_1_nonminimal_constant_time_branch
      hχ ha hb hT hsol ht₀_pos ht₀_T hsup hw
  · intro ha hb T hT u v hsol
    obtain ⟨w, hw⟩ := hminimal ha hb hT hsol
    exact Lemma_3_1_minimal_constant_time_branch
      hχ ha hb hT hsol hw

/-! ### Parabolic max-principle structure

`BoundedDomainData` alone is too weak to imply the parabolic max principle
for the sup norm — `not_forall_Lemma_3_1` exhibits a counterexample.  The
`ParabolicMaxPrincipleData D p` structure below bundles three primitive
analytic ingredients:

1. temporal continuity of `D.supNorm ∘ u` (a regularity hypothesis on the
   abstract `D.supNorm` field, more primitive than antitonicity);
2. pointwise nonpositive derivative of `D.supNorm ∘ u` at times where the
   sup exceeds the carrying capacity threshold (the non-minimal branch);
3. pointwise nonpositive derivative throughout time (the minimal branch).

`Lemma_3_1_of_parabolicMaxPrinciple` derives the global antitonicity
conclusion from these pointwise facts via Mathlib's mean-value theorem,
plus a continuity-based argument that the sup stays above threshold on the
whole prior interval. -/

/-- Primitive analytic axioms for the parabolic max principle of the
chemotaxis-logistic system on a bounded domain.  Conclusion is `Lemma_3_1 D p`
proved in `Lemma_3_1_of_parabolicMaxPrinciple`. -/
structure ParabolicMaxPrincipleData
    (D : BoundedDomainData) (p : CM2Params) where
  /-- The sup-norm `t ↦ D.supNorm (u t)` is continuous on the open time
  interval `(0, T)` for every classical solution `u`. -/
  supNorm_continuous_in_time :
    ∀ T : ℝ, 0 < T → ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
        ContinuousOn (fun t : ℝ => D.supNorm (u t)) (Set.Ioo 0 T)
  /-- In the non-minimal branch (`a, b > 0` and `χ₀ ≤ 0`), the sup-norm
  has a nonpositive derivative at every time where it exceeds the carrying
  capacity threshold `(a/b)^{1/α}`. -/
  nonminimal_supNorm_hasDerivAt_nonpos :
    p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
    ∀ T : ℝ, 0 < T → ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
        (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t) →
          ∃ d : ℝ, d ≤ 0 ∧
            HasDerivAt (fun s : ℝ => D.supNorm (u s)) d t
  /-- In the minimal branch (`a = b = 0` and `χ₀ ≤ 0`), the sup-norm has
  a nonpositive derivative everywhere on `(0, T)`. -/
  minimal_supNorm_hasDerivAt_nonpos :
    p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
    ∀ T : ℝ, 0 < T → ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) T →
        ∃ d : ℝ, d ≤ 0 ∧
          HasDerivAt (fun s : ℝ => D.supNorm (u s)) d t

/-- Helper: under continuous `M` on `(0, T)` and the pointwise-nonpositive-derivative
hypothesis above a threshold, the threshold persists backwards through `(0, t₀]`
whenever it is exceeded at `t₀`.  Proved by a `sSup` closed-set argument plus
Mathlib's `antitoneOn_of_deriv_nonpos`. -/
lemma threshold_persists_below_of_hasDerivAt_nonpos
    {M : ℝ → ℝ} {t₀ threshold T : ℝ}
    (ht₀_pos : 0 < t₀) (ht₀_T : t₀ < T)
    (hM_cont : ContinuousOn M (Set.Ioo 0 T))
    (hM_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) T, threshold < M t →
      ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt M d t)
    (hM_t₀ : threshold < M t₀) :
    ∀ t ∈ Set.Ioc (0 : ℝ) t₀, threshold < M t := by
  intro t ht
  obtain ⟨ht_pos, ht_le⟩ := ht
  by_contra h_le
  push_neg at h_le
  -- h_le : M t ≤ threshold; M t₀ > threshold ⇒ t ≠ t₀
  have ht_lt_t₀ : t < t₀ := by
    rcases lt_or_eq_of_le ht_le with h | h
    · exact h
    · exfalso
      rw [h] at h_le
      linarith
  -- Closed bounded nonempty set S of times in [t, t₀] where M ≤ threshold
  set S : Set ℝ := Set.Icc t t₀ ∩ M ⁻¹' Set.Iic threshold with hS_def
  have ht_in_S : t ∈ S := ⟨⟨le_refl t, ht_le⟩, h_le⟩
  have hS_bdd : BddAbove S := ⟨t₀, fun s hs => hs.1.2⟩
  have hS_ne : S.Nonempty := ⟨t, ht_in_S⟩
  -- M continuous on Icc t t₀ via restriction
  have hIcc_sub_Ioo : Set.Icc t t₀ ⊆ Set.Ioo (0 : ℝ) T := fun s ⟨h1, h2⟩ =>
    ⟨lt_of_lt_of_le ht_pos h1, lt_of_le_of_lt h2 ht₀_T⟩
  have hM_cont_Icc : ContinuousOn M (Set.Icc t t₀) := hM_cont.mono hIcc_sub_Ioo
  -- S is closed
  have hS_closed : IsClosed S :=
    hM_cont_Icc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  -- Sup of S is in S (closed bounded nonempty in ℝ)
  set s_star := sSup S with hs_star_def
  have hs_star_mem : s_star ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
  obtain ⟨⟨hs_star_t_le, hs_star_le_t₀⟩, hs_star_M_raw⟩ := hs_star_mem
  have hs_star_M : M s_star ≤ threshold := hs_star_M_raw
  -- s_star < t₀ since M s_star ≤ threshold < M t₀
  have hs_star_lt_t₀ : s_star < t₀ := by
    rcases lt_or_eq_of_le hs_star_le_t₀ with h | h
    · exact h
    · exfalso
      rw [h] at hs_star_M
      linarith
  -- For s ∈ Ioc s_star t₀, M s > threshold (else s ∈ S, contradicting sup)
  have hM_gt_on_Ioc :
      ∀ s ∈ Set.Ioc s_star t₀, threshold < M s := by
    intro s ⟨hs_gt, hs_le⟩
    by_contra hM_le
    push_neg at hM_le
    have hs_in_S : s ∈ S := ⟨⟨le_trans hs_star_t_le hs_gt.le, hs_le⟩, hM_le⟩
    have := le_csSup hS_bdd hs_in_S
    linarith
  -- Apply antitoneOn_of_deriv_nonpos on Icc s_star t₀
  have hConvex : Convex ℝ (Set.Icc s_star t₀) := convex_Icc _ _
  have hIcc_sub_Ioo' : Set.Icc s_star t₀ ⊆ Set.Ioo (0 : ℝ) T := fun s ⟨h1, h2⟩ =>
    ⟨lt_of_lt_of_le ht_pos (le_trans hs_star_t_le h1),
      lt_of_le_of_lt h2 ht₀_T⟩
  have hM_cont_Icc' : ContinuousOn M (Set.Icc s_star t₀) :=
    hM_cont.mono hIcc_sub_Ioo'
  -- For each t' ∈ interior Icc s_star t₀ = Ioo s_star t₀: M > threshold, hence
  -- DifferentiableAt M t' with deriv ≤ 0.
  have hM_deriv_Ioo :
      ∀ t' ∈ Set.Ioo s_star t₀,
        DifferentiableAt ℝ M t' ∧ deriv M t' ≤ 0 := by
    intro t' ht'
    have ht'_in_Ioc : t' ∈ Set.Ioc s_star t₀ := ⟨ht'.1, ht'.2.le⟩
    have ht'_gt : threshold < M t' := hM_gt_on_Ioc t' ht'_in_Ioc
    have ht'_in_Ioo : t' ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le ht_pos (le_trans hs_star_t_le ht'.1.le),
        lt_of_lt_of_le ht'.2 ht₀_T.le⟩
    obtain ⟨d, hd_nonpos, hd⟩ := hM_deriv t' ht'_in_Ioo ht'_gt
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    exact hd_nonpos
  have hDiff_Ioo : DifferentiableOn ℝ M (Set.Ioo s_star t₀) := fun t' ht' =>
    (hM_deriv_Ioo t' ht').1.differentiableWithinAt
  have hDeriv_nonpos : ∀ t' ∈ interior (Set.Icc s_star t₀), deriv M t' ≤ 0 := by
    intro t' ht'
    rw [interior_Icc] at ht'
    exact (hM_deriv_Ioo t' ht').2
  have hAntitone : AntitoneOn M (Set.Icc s_star t₀) := by
    apply antitoneOn_of_deriv_nonpos hConvex hM_cont_Icc'
    · rw [interior_Icc]
      exact hDiff_Ioo
    · exact hDeriv_nonpos
  -- Apply antitone at s_star and t₀
  have : M t₀ ≤ M s_star := hAntitone
    (Set.left_mem_Icc.mpr hs_star_le_t₀)
    (Set.right_mem_Icc.mpr hs_star_le_t₀)
    hs_star_le_t₀
  linarith

/-- **Real proof of Paper2 Lemma 3.1, conditional on `ParabolicMaxPrincipleData`.**

Given the primitive analytic axioms (sup-norm temporal continuity + pointwise
nonpositive derivative above threshold), the sup-norm is antitone on the
relevant time intervals, hence `SupNormNonincreasingOn` holds.  Proof uses
`threshold_persists_below_of_hasDerivAt_nonpos` to lift the conditional axiom
to a global differentiability statement on `(0, t₀]`, then applies
Mathlib's `antitoneOn_of_deriv_nonpos` on each subinterval. -/
theorem Lemma_3_1_of_parabolicMaxPrinciple
    {D : BoundedDomainData} {p : CM2Params}
    (h : ParabolicMaxPrincipleData D p) :
    Lemma_3_1 D p := by
  intro hχ
  refine ⟨?_, ?_⟩
  · -- Non-minimal branch: 0 < a, 0 < b, M(t₀) > threshold ⇒ M antitone on (0, t₀]
    intro ha hb T hT u v hsol t₀ ht₀_pos ht₀_T hsup
    set M := fun t : ℝ => D.supNorm (u t) with hM_def
    set threshold := (p.a / p.b) ^ (1 / p.α) with hthr_def
    have hM_cont : ContinuousOn M (Set.Ioo 0 T) :=
      h.supNorm_continuous_in_time T hT u v hsol
    have hM_deriv :
        ∀ t ∈ Set.Ioo (0 : ℝ) T, threshold < M t →
          ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt M d t := by
      intro t ht_in_Ioo hM_gt
      exact h.nonminimal_supNorm_hasDerivAt_nonpos hχ ha hb T hT u v hsol t
        ht_in_Ioo hM_gt
    -- Apply threshold persistence: M > threshold throughout (0, t₀]
    have hAbove : ∀ t ∈ Set.Ioc (0 : ℝ) t₀, threshold < M t :=
      threshold_persists_below_of_hasDerivAt_nonpos
        ht₀_pos ht₀_T hM_cont hM_deriv hsup
    -- Now show SupNormNonincreasingOn = AntitoneOn for M on Ioc 0 t₀
    intro t₁ ht₁ t₂ ht₂ ht_le
    -- Show M t₂ ≤ M t₁ via antitoneOn_of_deriv_nonpos on Icc t₁ t₂
    have ht₁_pos : 0 < t₁ := ht₁.1
    have ht₂_le : t₂ ≤ t₀ := ht₂.2
    have ht₁_in_Ioc : t₁ ∈ Set.Ioc (0 : ℝ) t₀ := ht₁
    have ht₂_in_Ioc : t₂ ∈ Set.Ioc (0 : ℝ) t₀ := ht₂
    have hIcc_sub_Ioo : Set.Icc t₁ t₂ ⊆ Set.Ioo (0 : ℝ) T := fun s ⟨h1, h2⟩ =>
      ⟨lt_of_lt_of_le ht₁_pos h1, lt_of_le_of_lt (le_trans h2 ht₂_le) ht₀_T⟩
    have hIcc_sub_Ioc : Set.Icc t₁ t₂ ⊆ Set.Ioc (0 : ℝ) t₀ := fun s ⟨h1, h2⟩ =>
      ⟨lt_of_lt_of_le ht₁_pos h1, le_trans h2 ht₂_le⟩
    have hM_cont_Icc : ContinuousOn M (Set.Icc t₁ t₂) :=
      hM_cont.mono hIcc_sub_Ioo
    have hM_deriv_Ioo :
        ∀ t ∈ Set.Ioo t₁ t₂,
          DifferentiableAt ℝ M t ∧ deriv M t ≤ 0 := by
      intro t ht
      have ht_in_Ioc : t ∈ Set.Ioc (0 : ℝ) t₀ := hIcc_sub_Ioc ⟨ht.1.le, ht.2.le⟩
      have ht_gt : threshold < M t := hAbove t ht_in_Ioc
      have ht_in_Ioo : t ∈ Set.Ioo (0 : ℝ) T :=
        hIcc_sub_Ioo ⟨ht.1.le, ht.2.le⟩
      obtain ⟨d, hd_nonpos, hd⟩ := hM_deriv t ht_in_Ioo ht_gt
      refine ⟨hd.differentiableAt, ?_⟩
      rw [hd.deriv]
      exact hd_nonpos
    have hDiff_Ioo : DifferentiableOn ℝ M (Set.Ioo t₁ t₂) := fun t' ht' =>
      (hM_deriv_Ioo t' ht').1.differentiableWithinAt
    have hDeriv_nonpos :
        ∀ t' ∈ interior (Set.Icc t₁ t₂), deriv M t' ≤ 0 := by
      intro t' ht'
      rw [interior_Icc] at ht'
      exact (hM_deriv_Ioo t' ht').2
    have hAntitone : AntitoneOn M (Set.Icc t₁ t₂) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hM_cont_Icc
      · rw [interior_Icc]; exact hDiff_Ioo
      · exact hDeriv_nonpos
    exact hAntitone
      (Set.left_mem_Icc.mpr ht_le)
      (Set.right_mem_Icc.mpr ht_le)
      ht_le
  · -- Minimal branch: a = b = 0, M antitone on (0, T)
    intro ha hb T hT u v hsol
    set M := fun t : ℝ => D.supNorm (u t) with hM_def
    have hM_cont : ContinuousOn M (Set.Ioo 0 T) :=
      h.supNorm_continuous_in_time T hT u v hsol
    intro t₁ ht₁ t₂ ht₂ ht_le
    have ht₁_pos : 0 < t₁ := ht₁.1
    have ht₁_lt_T : t₁ < T := ht₁.2
    have ht₂_pos : 0 < t₂ := ht₂.1
    have ht₂_lt_T : t₂ < T := ht₂.2
    have hIcc_sub_Ioo : Set.Icc t₁ t₂ ⊆ Set.Ioo (0 : ℝ) T := fun s ⟨h1, h2⟩ =>
      ⟨lt_of_lt_of_le ht₁_pos h1, lt_of_le_of_lt h2 ht₂_lt_T⟩
    have hM_cont_Icc : ContinuousOn M (Set.Icc t₁ t₂) :=
      hM_cont.mono hIcc_sub_Ioo
    have hM_deriv_Ioo :
        ∀ t ∈ Set.Ioo t₁ t₂,
          DifferentiableAt ℝ M t ∧ deriv M t ≤ 0 := by
      intro t ht
      have ht_in_Ioo : t ∈ Set.Ioo (0 : ℝ) T :=
        hIcc_sub_Ioo ⟨ht.1.le, ht.2.le⟩
      obtain ⟨d, hd_nonpos, hd⟩ :=
        h.minimal_supNorm_hasDerivAt_nonpos hχ ha hb T hT u v hsol t ht_in_Ioo
      refine ⟨hd.differentiableAt, ?_⟩
      rw [hd.deriv]
      exact hd_nonpos
    have hDiff_Ioo : DifferentiableOn ℝ M (Set.Ioo t₁ t₂) := fun t' ht' =>
      (hM_deriv_Ioo t' ht').1.differentiableWithinAt
    have hDeriv_nonpos :
        ∀ t' ∈ interior (Set.Icc t₁ t₂), deriv M t' ≤ 0 := by
      intro t' ht'
      rw [interior_Icc] at ht'
      exact (hM_deriv_Ioo t' ht').2
    have hAntitone : AntitoneOn M (Set.Icc t₁ t₂) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hM_cont_Icc
      · rw [interior_Icc]; exact hDiff_Ioo
      · exact hDeriv_nonpos
    exact hAntitone
      (Set.left_mem_Icc.mpr ht_le)
      (Set.right_mem_Icc.mpr ht_le)
      ht_le

/-- Paper2 Lemma 3.1 on the certified unit interval domain.  The interval
regularity component supplies the nonpositive derivative certificate for the
sup-norm profile, and `ParabolicMaxPrincipleData` turns that certificate into
monotonicity. -/
theorem Lemma_3_1_intervalDomain (p : CM2Params) :
    Lemma_3_1 ShenWork.IntervalDomain.intervalDomain p := by
  intro hχ
  constructor
  · intro ha hb T hT u v hsol t₀ ht₀_pos ht₀_T hsup
    have hreg :
        ShenWork.IntervalDomain.intervalDomainClassicalRegularity T u v := by
      simpa [ShenWork.IntervalDomain.intervalDomain] using hsol.2.1
    have hcert :=
      hreg.1 p hχ ha hb t₀ ht₀_pos ht₀_T (by
        simpa [ShenWork.IntervalDomain.intervalDomain] using hsup)
    have hcont :
        ContinuousOn
          (fun t => ShenWork.IntervalDomain.intervalDomain.supNorm (u t))
          (Set.Ioc (0 : ℝ) t₀) := by
      simpa [ShenWork.IntervalDomain.intervalDomain] using hcert.continuousOn
    have hdiff :
        DifferentiableOn ℝ
          (fun t => ShenWork.IntervalDomain.intervalDomain.supNorm (u t))
          (interior (Set.Ioc (0 : ℝ) t₀)) := by
      simpa [ShenWork.IntervalDomain.intervalDomain] using hcert.differentiableOn
    have hderiv :
        ∀ t, t ∈ interior (Set.Ioc (0 : ℝ) t₀) →
          deriv
            (fun s => ShenWork.IntervalDomain.intervalDomain.supNorm (u s)) t ≤
            0 := by
      intro t ht
      simpa [ShenWork.IntervalDomain.intervalDomain] using hcert.deriv_nonpos t ht
    exact
      SupNormAntitoneData.supNorm_nonincreasing_of_deriv_nonpos
        (D := ShenWork.IntervalDomain.intervalDomain)
        (u := u) (I := Set.Ioc (0 : ℝ) t₀)
        (convex_Ioc (0 : ℝ) t₀) hcont hdiff hderiv
  · intro ha hb T hT u v hsol
    have hreg :
        ShenWork.IntervalDomain.intervalDomainClassicalRegularity T u v := by
      simpa [ShenWork.IntervalDomain.intervalDomain] using hsol.2.1
    have hcert := hreg.2 p hχ ha hb
    have hcont :
        ContinuousOn
          (fun t => ShenWork.IntervalDomain.intervalDomain.supNorm (u t))
          (Set.Ioo (0 : ℝ) T) := by
      simpa [ShenWork.IntervalDomain.intervalDomain] using hcert.continuousOn
    have hdiff :
        DifferentiableOn ℝ
          (fun t => ShenWork.IntervalDomain.intervalDomain.supNorm (u t))
          (interior (Set.Ioo (0 : ℝ) T)) := by
      simpa [ShenWork.IntervalDomain.intervalDomain] using hcert.differentiableOn
    have hderiv :
        ∀ t, t ∈ interior (Set.Ioo (0 : ℝ) T) →
          deriv
            (fun s => ShenWork.IntervalDomain.intervalDomain.supNorm (u s)) t ≤
            0 := by
      intro t ht
      simpa [ShenWork.IntervalDomain.intervalDomain] using hcert.deriv_nonpos t ht
    exact
      SupNormAntitoneData.supNorm_nonincreasing_of_deriv_nonpos
        (D := ShenWork.IntervalDomain.intervalDomain)
        (u := u) (I := Set.Ioo (0 : ℝ) T)
        (convex_Ioo (0 : ℝ) T) hcont hdiff hderiv

/-- A fake bounded-domain interface showing that Lemma 3.1 is not a consequence
of the current abstract API alone.  The fake time derivative is identically
zero, so the increasing spatially constant profile satisfies the abstract PDE,
while the fake `supNorm` records its increase. -/
def lemma31CounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => f ()
  infValue := fun f => f ()
  integral := fun _ => 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def lemma31CounterU : ℝ → lemma31CounterDomain.Point → ℝ :=
  fun t _ => t + 1

def lemma31CounterV : ℝ → lemma31CounterDomain.Point → ℝ :=
  fun t _ => t + 1

lemma lemma31Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution lemma31CounterDomain
      proposition24CounterParams T lemma31CounterU lemma31CounterV := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    dsimp [lemma31CounterU]
    linarith
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition24CounterParams.χ₀ * 0 +
        (t + 1) * (proposition24CounterParams.a -
          proposition24CounterParams.b *
            (t + 1) ^ proposition24CounterParams.α)
    norm_num [proposition24CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - proposition24CounterParams.μ * (t + 1) +
        proposition24CounterParams.ν *
          (t + 1) ^ proposition24CounterParams.γ
    norm_num [proposition24CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma not_forall_Lemma_3_1 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Lemma_3_1 D p) := by
  intro h
  have hprop := h lemma31CounterDomain proposition24CounterParams
  have hmono :=
    (hprop (by norm_num [proposition24CounterParams])).2 rfl rfl
      1 (by norm_num) lemma31CounterU lemma31CounterV
      (lemma31Counter_classical 1 (by norm_num))
  have hbad :=
    hmono (1 / 4) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  simp [lemma31CounterDomain, lemma31CounterU] at hbad
  norm_num at hbad

/-- A separate fake interface refuting the first, `a,b > 0`, branch of
Lemma 3.1.  The abstract `timeDeriv` field is chosen to match the logistic
reaction of the increasing profile, so the stated PDE holds while the
abstract sup norm increases. -/
def lemma31NonminimalCounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => f ()
  infValue := fun f => f ()
  integral := fun _ => 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun w t _ => (w t ()) * (1 - w t ())
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def lemma31NonminimalCounterParams : CM2Params where
  N := 1
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
  hβ := by norm_num

def lemma31NonminimalCounterU :
    ℝ → lemma31NonminimalCounterDomain.Point → ℝ :=
  fun t _ => t + 1

def lemma31NonminimalCounterV :
    ℝ → lemma31NonminimalCounterDomain.Point → ℝ :=
  fun t _ => t + 1

lemma lemma31NonminimalCounter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution lemma31NonminimalCounterDomain
      lemma31NonminimalCounterParams T
      lemma31NonminimalCounterU lemma31NonminimalCounterV := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    dsimp [lemma31NonminimalCounterU]
    linarith
  · intro t x ht0 htT hx
    change (t + 1) * (1 - (t + 1)) =
      0 - 0 * 0 + (t + 1) * (1 - 1 * (t + 1) ^ (1 : ℝ))
    rw [Real.rpow_one]
    ring
  · intro t x ht0 htT hx
    change (0 : ℝ) = 0 - 1 * (t + 1) + 1 * (t + 1) ^ (1 : ℝ)
    rw [Real.rpow_one]
    ring
  · intro t x ht0 htT hx
    cases hx

lemma not_forall_Lemma_3_1_nonminimal_branch :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p T u v →
            ∀ t₀, 0 < t₀ → t₀ < T →
              (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t₀) →
                SupNormNonincreasingOn D u (Set.Ioc (0 : ℝ) t₀)) := by
  intro h
  have hmono :=
    h lemma31NonminimalCounterDomain lemma31NonminimalCounterParams
      (by norm_num [lemma31NonminimalCounterParams])
      (by norm_num [lemma31NonminimalCounterParams])
      (by norm_num [lemma31NonminimalCounterParams])
      1 (by norm_num) lemma31NonminimalCounterU lemma31NonminimalCounterV
      (lemma31NonminimalCounter_classical 1 (by norm_num))
      (1 / 2) (by norm_num) (by norm_num) ?_
  · have hbad :=
      hmono (1 / 4) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    simp [lemma31NonminimalCounterDomain, lemma31NonminimalCounterU] at hbad
    norm_num at hbad
  · norm_num [lemma31NonminimalCounterParams]
    dsimp [lemma31NonminimalCounterDomain, lemma31NonminimalCounterU]
    norm_num

/-- Concrete minimal-branch counterexample to the current abstract-domain
formulation of Paper2 Lemma 3.1. -/
lemma not_Lemma_3_1_minimal_counter :
    ¬ Lemma_3_1 lemma31CounterDomain proposition24CounterParams := by
  intro h
  have hmono :=
    (h (by norm_num [proposition24CounterParams])).2 rfl rfl
      1 (by norm_num) lemma31CounterU lemma31CounterV
      (lemma31Counter_classical 1 (by norm_num))
  have hbad :=
    hmono (1 / 4) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  simp [lemma31CounterDomain, lemma31CounterU] at hbad
  norm_num at hbad

/-- Concrete positive-logistic-branch counterexample to the current
abstract-domain formulation of Paper2 Lemma 3.1. -/
lemma not_Lemma_3_1_nonminimal_counter :
    ¬ Lemma_3_1 lemma31NonminimalCounterDomain
      lemma31NonminimalCounterParams := by
  intro h
  have hmono :=
    (h (by norm_num [lemma31NonminimalCounterParams])).1
      (by norm_num [lemma31NonminimalCounterParams])
      (by norm_num [lemma31NonminimalCounterParams])
      1 (by norm_num) lemma31NonminimalCounterU lemma31NonminimalCounterV
      (lemma31NonminimalCounter_classical 1 (by norm_num))
      (1 / 2) (by norm_num) (by norm_num) ?_
  · have hbad :=
      hmono (1 / 4) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    simp [lemma31NonminimalCounterDomain, lemma31NonminimalCounterU] at hbad
    norm_num at hbad
  · norm_num [lemma31NonminimalCounterParams]
    dsimp [lemma31NonminimalCounterDomain, lemma31NonminimalCounterU]
    norm_num

def Lemma_4_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      InitialTrace D u₀ u →
        ∀ eps > 0, ∀ pExp > 1, ∃ Ceps > 0,
          LpMassGradientInterpolationEstimate D pExp eps Ceps T u

/-- A fake bounded-domain interface showing that Lemma 4.1's interpolation
estimate is not a consequence of the current abstract API alone.  The constant
profile `u = v = 2` solves the fake PDE, while the fake integral assigns mass
to `u^2` but not to `u` or the zero gradient term. -/
def lemma41CounterDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => |f ()|
  infValue := fun f => f ()
  integral := fun f => if f () = (4 : ℝ) then 1 else 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => True

def lemma41CounterParams : CM2Params where
  N := 1
  hN := by norm_num
  α := 1
  γ := 1
  m := 1
  μ := 1
  ν := 1
  χ₀ := 0
  a := 2
  b := 1
  β := 0
  hα := by norm_num
  hγ := by norm_num
  hm := by norm_num
  hμ := by norm_num
  hν := by norm_num
  ha := by norm_num
  hb := by norm_num
  hβ := by norm_num

def lemma41CounterU0 : lemma41CounterDomain.Point → ℝ :=
  fun _ => 2

def lemma41CounterU : ℝ → lemma41CounterDomain.Point → ℝ :=
  fun _ _ => 2

def lemma41CounterV : ℝ → lemma41CounterDomain.Point → ℝ :=
  fun _ _ => 2

lemma lemma41Counter_initial :
    PositiveInitialDatum lemma41CounterDomain lemma41CounterU0 := by
  constructor
  · trivial
  · intro x hx
    norm_num [lemma41CounterU0]

lemma lemma41Counter_trace :
    InitialTrace lemma41CounterDomain lemma41CounterU0 lemma41CounterU := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro t ht0 htδ
  simpa [lemma41CounterDomain, lemma41CounterU0, lemma41CounterU] using hε

lemma lemma41Counter_classical (T : ℝ) (hT : 0 < T) :
    IsPaper2ClassicalSolution lemma41CounterDomain lemma41CounterParams T
      lemma41CounterU lemma41CounterV := by
  refine ⟨hT, trivial, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT hx
    norm_num [lemma41CounterU]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - lemma41CounterParams.χ₀ * 0 +
        2 * (lemma41CounterParams.a -
          lemma41CounterParams.b * (2 : ℝ) ^ lemma41CounterParams.α)
    norm_num [lemma41CounterParams]
  · intro t x ht0 htT hx
    change (0 : ℝ) =
      0 - lemma41CounterParams.μ * 2 +
        lemma41CounterParams.ν * (2 : ℝ) ^ lemma41CounterParams.γ
    norm_num [lemma41CounterParams]
  · intro t x ht0 htT hx
    cases hx

lemma not_forall_Lemma_4_1 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Lemma_4_1 D p) := by
  intro h
  have hprop := h lemma41CounterDomain lemma41CounterParams
  rcases hprop lemma41CounterU0 lemma41Counter_initial
      1 (by norm_num) lemma41CounterU lemma41CounterV
      (lemma41Counter_classical 1 (by norm_num)) lemma41Counter_trace
      1 (by norm_num) 2 (by norm_num) with
    ⟨Ceps, _hCeps_pos, hestimate⟩
  have hbad := hestimate (1 / 2) (by norm_num) (by norm_num)
  simp [lemma41CounterDomain, lemma41CounterU] at hbad
  norm_num at hbad

structure Paper2Constants (p : CM2Params) where
  K : ℝ
  K_nonneg : 0 ≤ K

/-- Paper2 Remark 1.6 threshold `(1.30a)` in the slice
`m = 1`, `α = γ`, `β ≥ 1`. -/
def remark16ChiStar1 (p : CM2Params) (C : Paper2Constants p) : ℝ :=
  ((p.N : ℝ) * p.γ * p.b) /
    (((p.N : ℝ) * p.γ - 2) * (p.ν + Psi_beta p.β * C.K))

/-- Paper2 Remark 1.6 threshold `(1.30b)` in the slice
`m = 1`, `α = γ`, `β ≥ 1`. -/
def remark16ChiStar2 (p : CM2Params) (C : Paper2Constants p) : ℝ :=
  Real.sqrt
    (8 * p.b /
      (((p.N : ℝ) * p.γ - 2) * Theta_beta (2 * p.β - 1) * C.K))

lemma remark16ChiStar1_pos
    (p : CM2Params) (C : Paper2Constants p)
    (hβ : 0 ≤ p.β) (hb : 0 < p.b)
    (hdim : 2 < (p.N : ℝ) * p.γ) :
    0 < remark16ChiStar1 p C := by
  have hN_pos : 0 < (p.N : ℝ) := by
    exact_mod_cast p.hN
  have hnum_pos : 0 < (p.N : ℝ) * p.γ * p.b := by
    nlinarith [hN_pos, p.hγ, hb]
  have hpsi_nonneg : 0 ≤ Psi_beta p.β := Psi_beta_nonneg hβ
  have hinner_pos : 0 < p.ν + Psi_beta p.β * C.K := by
    have hmul_nonneg : 0 ≤ Psi_beta p.β * C.K :=
      mul_nonneg hpsi_nonneg C.K_nonneg
    linarith [p.hν, hmul_nonneg]
  have hden_pos :
      0 < ((p.N : ℝ) * p.γ - 2) *
        (p.ν + Psi_beta p.β * C.K) :=
    mul_pos (by linarith) hinner_pos
  unfold remark16ChiStar1
  exact div_pos hnum_pos hden_pos

lemma remark16ChiStar2_nonneg
    (p : CM2Params) (C : Paper2Constants p) :
    0 ≤ remark16ChiStar2 p C := by
  unfold remark16ChiStar2
  exact Real.sqrt_nonneg _

lemma remark16ChiStar2_pos_of_K_pos
    (p : CM2Params) (C : Paper2Constants p)
    (hβ : 1 ≤ p.β) (hb : 0 < p.b) (hK : 0 < C.K)
    (hdim : 2 < (p.N : ℝ) * p.γ) :
    0 < remark16ChiStar2 p C := by
  have htheta_pos : 0 < Theta_beta (2 * p.β - 1) :=
    Theta_beta_pos (by linarith)
  have hden_pos :
      0 <
        (((p.N : ℝ) * p.γ - 2) *
          Theta_beta (2 * p.β - 1) * C.K) := by
    exact mul_pos (mul_pos (by linarith) htheta_pos) hK
  have harg_pos :
      0 <
        8 * p.b /
          (((p.N : ℝ) * p.γ - 2) *
            Theta_beta (2 * p.β - 1) * C.K) := by
    exact div_pos (by nlinarith) hden_pos
  unfold remark16ChiStar2
  exact Real.sqrt_pos.mpr harg_pos

/-- Sign statement for the two strong Remark 1.6 thresholds `(1.30a)` and
`(1.30b)`.  The second threshold is nonnegative unconditionally because it is a
square root; strict positivity additionally needs the exposed constant `K` to
be positive. -/
theorem remark16StrongThreshold_sign_properties :
    (∀ p : CM2Params, ∀ C : Paper2Constants p,
      0 ≤ p.β → 0 < p.b → 2 < (p.N : ℝ) * p.γ →
        0 < remark16ChiStar1 p C) ∧
    (∀ p : CM2Params, ∀ C : Paper2Constants p,
      0 ≤ remark16ChiStar2 p C) ∧
    (∀ p : CM2Params, ∀ C : Paper2Constants p,
      1 ≤ p.β → 0 < p.b → 0 < C.K →
        2 < (p.N : ℝ) * p.γ →
          0 < remark16ChiStar2 p C) := by
  exact ⟨
    (fun p C hβ hb hdim => remark16ChiStar1_pos p C hβ hb hdim),
    (fun p C => remark16ChiStar2_nonneg p C),
    (fun p C hβ hb hK hdim =>
      remark16ChiStar2_pos_of_K_pos p C hβ hb hK hdim)⟩

/-- Paper2 Remark 1.6 threshold `(1.30c)`, identical to `χ_β`. -/
def remark16ChiStarWeak (p : CM2Params) : ℝ :=
  2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))

lemma remark16ChiStarWeak_eq_chiBeta (p : CM2Params) :
    remark16ChiStarWeak p = chiBeta p := by
  rfl

lemma remark16ChiStarWeak_pos_of_one_le_beta
    (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < remark16ChiStarWeak p := by
  simpa [remark16ChiStarWeak_eq_chiBeta] using
    chiBeta_pos_of_one_le_beta p hβ

lemma remark16ChiStarWeak_nonneg_of_half_le_beta
    (p : CM2Params) (hβ : (1 / 2 : ℝ) ≤ p.β) :
    0 ≤ remark16ChiStarWeak p := by
  simpa [remark16ChiStarWeak_eq_chiBeta] using
    chiBeta_nonneg_of_half_le_beta p hβ

lemma remark16ChiStarWeak_min_half_sqrt_pos_of_one_le_beta
    (p : CM2Params) (hβ : 1 ≤ p.β) :
    0 < min (remark16ChiStarWeak p / 2)
      (Real.sqrt (remark16ChiStarWeak p)) := by
  simpa [remark16ChiStarWeak_eq_chiBeta] using
    min_chiBeta_half_sqrt_pos_of_one_le_beta p hβ

lemma lt_remark16ChiStarWeak_of_lt_min_half_sqrt
    (p : CM2Params) {chi : ℝ} (hβ : 1 ≤ p.β)
    (hchi :
      chi < min (remark16ChiStarWeak p / 2)
        (Real.sqrt (remark16ChiStarWeak p))) :
    chi < remark16ChiStarWeak p := by
  simpa [remark16ChiStarWeak_eq_chiBeta] using
    lt_chiBeta_of_lt_min_half_sqrt p hβ
      (by simpa [remark16ChiStarWeak_eq_chiBeta] using hchi)

lemma remark16ChiStarWeak_le_two_beta_sub_one
    (p : CM2Params) (hβ : (1 / 2 : ℝ) ≤ p.β) :
    remark16ChiStarWeak p ≤ 2 * p.β - 1 := by
  simpa [remark16ChiStarWeak_eq_chiBeta] using
    chiBeta_le_two_beta_sub_one p hβ

lemma remark16ChiStarWeak_eq_two_beta_sub_one_of_gamma_mul_N_le_two
    (p : CM2Params) (hden : p.γ * (p.N : ℝ) ≤ 2) :
    remark16ChiStarWeak p = 2 * p.β - 1 := by
  simpa [remark16ChiStarWeak_eq_chiBeta] using
    chiBeta_eq_two_beta_sub_one_of_gamma_mul_N_le_two p hden

lemma remark16ChiStarWeak_lt_two_beta_sub_one_of_two_lt_gamma_mul_N
    (p : CM2Params) (hβ : (1 / 2 : ℝ) < p.β)
    (hden : (2 : ℝ) < p.γ * (p.N : ℝ)) :
    remark16ChiStarWeak p < 2 * p.β - 1 := by
  simpa [remark16ChiStarWeak_eq_chiBeta] using
    chiBeta_lt_two_beta_sub_one_of_two_lt_gamma_mul_N p hβ hden

/-- End-to-end scalar statement for the weak Remark 1.6 threshold `(1.30c)`.
It records positivity, the smallness implication used by Theorem 1.2, and the
comparison with the elementary threshold `2β - 1`. -/
theorem remark16ChiStarWeak_scalar_properties :
    (∀ p : CM2Params, 1 ≤ p.β →
      0 < remark16ChiStarWeak p ∧
        0 < min (remark16ChiStarWeak p / 2)
          (Real.sqrt (remark16ChiStarWeak p))) ∧
    (∀ p : CM2Params, ∀ chi : ℝ, 1 ≤ p.β →
      chi < min (remark16ChiStarWeak p / 2)
        (Real.sqrt (remark16ChiStarWeak p)) →
      chi < remark16ChiStarWeak p) ∧
    (∀ p : CM2Params, (1 / 2 : ℝ) ≤ p.β →
      0 ≤ remark16ChiStarWeak p ∧
        remark16ChiStarWeak p ≤ 2 * p.β - 1) ∧
    (∀ p : CM2Params, p.γ * (p.N : ℝ) ≤ 2 →
      remark16ChiStarWeak p = 2 * p.β - 1) ∧
    (∀ p : CM2Params, (1 / 2 : ℝ) < p.β →
      (2 : ℝ) < p.γ * (p.N : ℝ) →
        remark16ChiStarWeak p < 2 * p.β - 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hβ
    exact ⟨remark16ChiStarWeak_pos_of_one_le_beta p hβ,
      remark16ChiStarWeak_min_half_sqrt_pos_of_one_le_beta p hβ⟩
  · intro p chi hβ hchi
    exact lt_remark16ChiStarWeak_of_lt_min_half_sqrt p hβ hchi
  · intro p hβ
    exact ⟨remark16ChiStarWeak_nonneg_of_half_le_beta p hβ,
      remark16ChiStarWeak_le_two_beta_sub_one p hβ⟩
  · intro p hden
    exact remark16ChiStarWeak_eq_two_beta_sub_one_of_gamma_mul_N_le_two p hden
  · intro p hβ hden
    exact
      remark16ChiStarWeak_lt_two_beta_sub_one_of_two_lt_gamma_mul_N
        p hβ hden

def StrongLogisticCondition (p : CM2Params) (C : Paper2Constants p) : Prop :=
  (p.β ≥ 0 ∧ p.α > p.m + p.γ - 1) ∨
    (p.β ≥ 1 / 2 ∧ p.α > 2 * p.m + p.γ - 2) ∨
    (p.β ≥ 0 ∧ p.α = p.m + p.γ - 1 ∧
      (positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K)))) ∨
    (p.β ≥ 1 / 2 ∧ p.α = 2 * p.m + p.γ - 2 ∧
      (positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K))))

lemma StrongLogisticCondition.of_alpha_gt_m_add_gamma_sub_one
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 0 ≤ p.β) (hα : p.m + p.γ - 1 < p.α) :
    StrongLogisticCondition p C := by
  exact Or.inl ⟨hβ, hα⟩

lemma StrongLogisticCondition.of_alpha_gt_two_mul_m_add_gamma_sub_two
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : 2 * p.m + p.γ - 2 < p.α) :
    StrongLogisticCondition p C := by
  exact Or.inr (Or.inl ⟨hβ, hα⟩)

lemma StrongLogisticCondition.of_critical_m_add_gamma_sub_one
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 0 ≤ p.β)
    (hα : p.α = p.m + p.γ - 1)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K))) :
    StrongLogisticCondition p C := by
  exact Or.inr (Or.inr (Or.inl ⟨hβ, hα, hχ⟩))

lemma StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K))) :
    StrongLogisticCondition p C := by
  exact Or.inr (Or.inr (Or.inr ⟨hβ, hα, hχ⟩))

lemma StrongLogisticCondition.of_critical_m_add_gamma_sub_one_low_dimension
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 0 ≤ p.β)
    (hα : p.α = p.m + p.γ - 1)
    (hdim : (p.N : ℝ) * p.α ≤ 2) :
    StrongLogisticCondition p C := by
  exact
    StrongLogisticCondition.of_critical_m_add_gamma_sub_one hβ hα
      (Or.inl (positivePart_eq_zero_of_nonpos (by linarith)))

lemma StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two_low_dimension
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hdim : (p.N : ℝ) * p.α ≤ 2) :
    StrongLogisticCondition p C := by
  exact
    StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two hβ hα
      (Or.inl (positivePart_eq_zero_of_nonpos (by linarith)))

lemma StrongLogisticCondition.of_remark16_chiStar1
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar1 p C) :
    StrongLogisticCondition p C := by
  have hβ0 : 0 ≤ p.β := by linarith
  have hcrit : p.α = p.m + p.γ - 1 := by
    rw [hα, hm]
    ring
  refine StrongLogisticCondition.of_critical_m_add_gamma_sub_one hβ0 hcrit ?_
  right
  have hpospart :
      positivePart ((p.N : ℝ) * p.α - 2) = (p.N : ℝ) * p.γ - 2 := by
    rw [hα]
    exact positivePart_eq_self_of_nonneg (by linarith)
  rw [hpospart, hm]
  convert hχ using 1
  unfold remark16ChiStar1
  ring

lemma StrongLogisticCondition.of_remark16_chiStar2
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar2 p C) :
    StrongLogisticCondition p C := by
  have hβ_half : (1 / 2 : ℝ) ≤ p.β := by linarith
  have hcrit : p.α = 2 * p.m + p.γ - 2 := by
    rw [hα, hm]
    ring
  refine
    StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two
      hβ_half hcrit ?_
  right
  have hpospart :
      positivePart ((p.N : ℝ) * p.α - 2) = (p.N : ℝ) * p.γ - 2 := by
    rw [hα]
    exact positivePart_eq_self_of_nonneg (by linarith)
  rw [hpospart]
  simpa [remark16ChiStar2] using hχ

lemma StrongLogisticCondition.of_remark16_min_chiStar12
    {p : CM2Params} {C : Paper2Constants p}
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < min (remark16ChiStar1 p C) (remark16ChiStar2 p C)) :
    StrongLogisticCondition p C :=
  StrongLogisticCondition.of_remark16_chiStar1 hβ hm hα hdim
    (lt_of_lt_of_le hχ (min_le_left _ _))

lemma StrongLogisticCondition.beta_nonneg
    {p : CM2Params} {C : Paper2Constants p}
    (h : StrongLogisticCondition p C) :
    0 ≤ p.β := by
  rcases h with h | h | h | h
  · exact h.1
  · linarith [h.1]
  · exact h.1
  · linarith [h.1]

lemma StrongLogisticCondition.alpha_ge_m_add_gamma_sub_one_of_m_ge_one
    {p : CM2Params} {C : Paper2Constants p}
    (hm : 1 ≤ p.m) (h : StrongLogisticCondition p C) :
    p.m + p.γ - 1 ≤ p.α := by
  rcases h with h | h | h | h
  · exact le_of_lt h.2
  · have hle : p.m + p.γ - 1 ≤ 2 * p.m + p.γ - 2 := by
      linarith
    exact le_trans hle (le_of_lt h.2)
  · linarith [h.2.1]
  · have hle : p.m + p.γ - 1 ≤ 2 * p.m + p.γ - 2 := by
      linarith
    linarith [hle, h.2.1]

lemma StrongLogisticCondition.alpha_ge_two_mul_m_add_gamma_sub_two_of_m_le_one
    {p : CM2Params} {C : Paper2Constants p}
    (hm : p.m ≤ 1) (h : StrongLogisticCondition p C) :
    2 * p.m + p.γ - 2 ≤ p.α := by
  rcases h with h | h | h | h
  · have hle : 2 * p.m + p.γ - 2 ≤ p.m + p.γ - 1 := by
      linarith
    exact le_trans hle (le_of_lt h.2)
  · exact le_of_lt h.2
  · have hle : 2 * p.m + p.γ - 2 ≤ p.m + p.γ - 1 := by
      linarith
    linarith [hle, h.2.1]
  · linarith [h.2.1]

/-- Paper2 Proposition 1.1: local existence and blow-up alternative. -/
def Proposition_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      FiniteHorizonAlternative D Tmax u ∧
      (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u)

/-- A deliberately degenerate bounded-domain API instance showing that the
current abstract interface alone cannot prove Paper2 Proposition 1.1 for every
`BoundedDomainData`.  The regularity field is `False`, so no classical solution
can exist even though every initial datum is admissible. -/
def proposition11NoRegularityDomain : BoundedDomainData where
  Point := Unit
  inside := ∅
  boundary := ∅
  volume := 1
  supNorm := fun _ => 0
  infValue := fun _ => 0
  integral := fun _ => 0
  gradNorm := fun _ _ => 0
  timeDeriv := fun _ _ _ => 0
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ _ _ => False

def proposition11CounterParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 0
    b := 0
    β := 0
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

lemma not_forall_Proposition_1_1 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Proposition_1_1 D p) := by
  intro h
  let D := proposition11NoRegularityDomain
  let p := proposition11CounterParams
  let u₀ : D.Point → ℝ := fun _ => 1
  have hu₀ : PositiveInitialDatum D u₀ := by
    constructor
    · trivial
    · intro x hx
      exact False.elim (by simpa [D, proposition11NoRegularityDomain] using hx)
  rcases h D p u₀ hu₀ with ⟨Tmax, _hTmax, u, v, hsol, _htrace, _halt⟩
  exact hsol.regularity

/-- Paper2 Theorem 1.1: boundedness/global existence for negative sensitivity. -/
def Theorem_1_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 →
    (0 < p.a → 0 < p.b →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          (∀ t, 0 < t → t < Tmax →
            D.supNorm (u t) ≤ max (D.supNorm u₀) ((p.a / p.b) ^ (1 / p.α))) ∧
          (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v)) ∧
    (p.a = 0 → p.b = 0 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          (∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ D.supNorm u₀) ∧
          (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v))

lemma not_forall_Theorem_1_1 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Theorem_1_1 D p) := by
  intro h
  let D := proposition11NoRegularityDomain
  let p := proposition11CounterParams
  let u₀ : D.Point → ℝ := fun _ => 1
  have hu₀ : PositiveInitialDatum D u₀ := by
    constructor
    · trivial
    · intro x hx
      exact False.elim (by simpa [D, proposition11NoRegularityDomain] using hx)
  rcases (h D p (by norm_num [p, proposition11CounterParams])).2 rfl rfl u₀ hu₀ with
    ⟨Tmax, _hTmax, u, v, hsol, _htrace, _hbound, _hglobal⟩
  exact hsol.regularity

def theorem12NoRegularityParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 1
    γ := 1
    m := 1
    μ := 1
    ν := 1
    χ₀ := 0
    a := 0
    b := 0
    β := 1
    hα := by norm_num
    hγ := by norm_num
    hm := by norm_num
    hμ := by norm_num
    hν := by norm_num
    ha := by norm_num
    hb := by norm_num
    hβ := by norm_num }

/-- Paper2 Theorem 1.2: boundedness/global existence for weak nonlinear cross diffusion. -/
def Theorem_1_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
    ((0 < p.m → p.m < 1 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2BoundedBefore D Tmax u) ∧
    (p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u))

lemma not_forall_Theorem_1_2 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params, Theorem_1_2 D p) := by
  intro h
  let D := proposition11NoRegularityDomain
  let p := theorem12NoRegularityParams
  let u₀ : D.Point → ℝ := fun _ => 1
  have hu₀ : PositiveInitialDatum D u₀ := by
    constructor
    · trivial
    · intro x hx
      exact False.elim (by simpa [D, proposition11NoRegularityDomain] using hx)
  have hχ : p.χ₀ < chiBeta p := by
    norm_num [p, theorem12NoRegularityParams, chiBeta]
  rcases (h D p (by norm_num [p, theorem12NoRegularityParams])
      (by norm_num [p, theorem12NoRegularityParams])
      (by norm_num [p, theorem12NoRegularityParams])).2
      (by norm_num [p, theorem12NoRegularityParams]) hχ u₀ hu₀ with
    ⟨u, v, hglobal, _htrace, _hbounded⟩
  exact hglobal.regularity (T := 1) (by norm_num)

def theorem13NoRegularityParams : CM2Params :=
  { N := 1
    hN := by norm_num
    α := 2
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

def theorem13NoRegularityConstants : Paper2Constants theorem13NoRegularityParams where
  K := 0
  K_nonneg := by norm_num

/-- Paper2 Theorem 1.3: boundedness/global existence under a strong logistic source. -/
def Theorem_1_3 (D : BoundedDomainData) (p : CM2Params) (C : Paper2Constants p) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
    (∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          IsPaper2BoundedBefore D Tmax u) ∧
    (1 ≤ p.m →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u)

lemma not_forall_Theorem_1_3 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
      ∀ C : Paper2Constants p, Theorem_1_3 D p C) := by
  intro h
  let D := proposition11NoRegularityDomain
  let p := theorem13NoRegularityParams
  let C := theorem13NoRegularityConstants
  let u₀ : D.Point → ℝ := fun _ => 1
  have hu₀ : PositiveInitialDatum D u₀ := by
    constructor
    · trivial
    · intro x hx
      exact False.elim (by simpa [D, proposition11NoRegularityDomain] using hx)
  have hcond : StrongLogisticCondition p C :=
    StrongLogisticCondition.of_alpha_gt_m_add_gamma_sub_one
      (by norm_num [p, theorem13NoRegularityParams])
      (by norm_num [p, theorem13NoRegularityParams])
  rcases (h D p C
      (by norm_num [p, theorem13NoRegularityParams])
      (by norm_num [p, theorem13NoRegularityParams])
      (by norm_num [p, theorem13NoRegularityParams])
      hcond).1 u₀ hu₀ with
    ⟨Tmax, _hTmax, u, v, hsol, _htrace, _hbounded⟩
  exact hsol.regularity

/-- **TAUTOLOGY (no math content)**: this closure's body is `:= hexist`,
i.e. it returns its hypothesis verbatim because the hypothesis is
definitionally equal to `Proposition_1_1 D p`.  Useful only as a target
signature when a real existence proof becomes available; do NOT cite as
mathematical progress. -/
theorem Proposition_1_1.of_assumed_existence_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hexist : ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p Tmax u v ∧
        InitialTrace D u₀ u ∧
        FiniteHorizonAlternative D Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u)) :
    Proposition_1_1 D p :=
  hexist

/-- **TAUTOLOGY (no math content)**: body is `:= hest`, definitionally equal
to `Lemma_4_1 D p`.  Target signature only; do NOT cite as math progress. -/
theorem Lemma_4_1.of_assumed_estimate_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hest : ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p T u v →
          InitialTrace D u₀ u →
            ∀ eps > 0, ∀ pExp > 1, ∃ Ceps > 0,
              LpMassGradientInterpolationEstimate D pExp eps Ceps T u) :
    Lemma_4_1 D p :=
  hest

/-- **TAUTOLOGY (no math content)**: body is `:= hbound`, definitionally
equal to `Lemma_2_6 D`.  Target signature only; do NOT cite as math progress. -/
theorem Lemma_2_6.of_assumed_bound_branch
    {D : BoundedDomainData}
    (hbound : ∀ N > 0, ∀ u : ℝ → D.Point → ℝ, ∀ T rho p0,
      AbstractLpBootstrapHypothesis D u N T rho p0 →
        LpBootstrapEnergyInequality D u T rho p0 →
          ∀ pExp > 1, LpPowerBoundedBefore D pExp T u) :
    Lemma_2_6 D :=
  hbound

/-- **TAUTOLOGY (no math content)**: body is `:= hbound`, definitionally
equal to `Lemma_2_7 D`.  Target signature only; do NOT cite as math progress. -/
theorem Lemma_2_7.of_assumed_bound_branch
    {D : BoundedDomainData}
    (hbound : ∀ u : ℝ → D.Point → ℝ, ∀ T pExp C1 C2 C3 C4 eps alpha,
      0 < T → 1 < pExp →
        0 ≤ C1 → 0 ≤ C2 → 0 ≤ C3 → 0 < C4 →
          0 < eps → eps ≤ alpha →
            (∀ t, 0 < t → t < T →
              deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
                  C3 * D.integral (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
                C1 + C2 * D.integral (fun x => (u t x) ^ pExp) -
                  C4 * D.integral (fun x => (u t x) ^ (pExp + alpha))) →
              LpPowerBoundedBefore D pExp T u) :
    Lemma_2_7 D :=
  hbound

/-- **TAUTOLOGY (no math content)**: body is `:= hbound`, definitionally
equal to `Corollary_2_1 D p`.  Target signature only. -/
theorem Corollary_2_1.of_assumed_bound_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hbound : ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
        (∃ rho > 0, CrossDiffusionBootstrapEstimate D p T rho u v ∧
          ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
            LpPowerBoundedBefore D p0 T u) →
        ∀ pExp > 1, LpPowerBoundedBefore D pExp T u) :
    Corollary_2_1 D p :=
  hbound

/-- **TAUTOLOGY (no math content)**: body is `:= hbound`, definitionally
equal to `Proposition_2_1 D p S`.  Target signature only. -/
theorem Proposition_2_1.of_assumed_bound_branch
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (hbound : ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
        ∀ pExp, 1 ≤ pExp →
          ∀ t, 0 < t → t < T →
            S.lpNorm pExp (v t) ≤
              (p.ν / p.μ) * S.lpNorm pExp (fun x => (u t x) ^ p.γ)) :
    Proposition_2_1 D p S :=
  hbound

/-- **TAUTOLOGY (no math content)**: body is `:= hest`, definitionally equal
to `Proposition_2_2 D p`.  Target signature only. -/
theorem Proposition_2_2.of_assumed_estimate_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hest : ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
        ∀ pExp > 1, ∃ Mstar > 0,
          WeightedGradientEstimate D pExp p.β p.γ Mstar T u v) :
    Proposition_2_2 D p :=
  hest

/-- **TAUTOLOGY (no math content)**: body is `:= hest`, definitionally equal
to `Proposition_2_3 D p`.  Target signature only. -/
theorem Proposition_2_3.of_assumed_estimate_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hest : ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p T u v →
        ∀ pExp, max 1 p.β < pExp →
          ∀ eps > 0, ∃ Ceps > 0,
            WeightedSignalEstimate D pExp p.β p.γ eps Ceps T u v) :
    Proposition_2_3 D p :=
  hest

/-- **TAUTOLOGY (no math content)**: body is `:= hmass`, definitionally equal
to `Proposition_2_4 D p`.  Target signature only. -/
theorem Proposition_2_4.of_assumed_mass_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hmass : ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p T u v →
        InitialTrace D u₀ u →
          (p.a = 0 → p.b = 0 → MassConservedBefore D T u₀ u) ∧
            (0 < p.a → 0 < p.b → LogisticMassUpperBoundBefore D p T u₀ u)) :
    Proposition_2_4 D p :=
  hmass

/-- **TAUTOLOGY (no math content)**: body is `:= hbound`, definitionally equal
to `Proposition_2_5 D p`.  Target signature only. -/
theorem Proposition_2_5.of_assumed_bound_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hbound : ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → D.Point → ℝ,
        IsPaper2ClassicalSolution D p Tmax u v →
        InitialTrace D u₀ u →
          ∀ pExp,
            max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
              LpPowerBoundedBefore D pExp Tmax u →
                IsPaper2BoundedBefore D Tmax u) :
    Proposition_2_5 D p :=
  hbound

/-- Generic existence-hypothesis closure for Paper 2 Theorem 1.1.
Given that the relevant Cauchy solution exists with the required `L∞` bound
and the global criterion `1 ≤ p.m` in both branches, `Theorem_1_1` follows. -/
theorem Theorem_1_1.of_assumed_solutions_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hnonminimal :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          (∀ t, 0 < t → t < Tmax →
            D.supNorm (u t) ≤ max (D.supNorm u₀) ((p.a / p.b) ^ (1 / p.α))) ∧
          (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v))
    (hminimal :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
          InitialTrace D u₀ u ∧
          (∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ D.supNorm u₀) ∧
          (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v)) :
    Theorem_1_1 D p := by
  intro hχ
  refine ⟨?_, ?_⟩
  · intro ha hb u₀ hu₀
    exact hnonminimal hχ ha hb u₀ hu₀
  · intro ha hb u₀ hu₀
    exact hminimal hχ ha hb u₀ hu₀

/-- Generic existence-hypothesis closure for Paper 2 Theorem 1.2. -/
theorem Theorem_1_2.of_assumed_solutions_branch
    {D : BoundedDomainData} {p : CM2Params}
    (hslow_diffusion :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      0 < p.m → p.m < 1 →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2BoundedBefore D Tmax u)
    (hcritical :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u) :
    Theorem_1_2 D p := by
  intro ha hb hβ
  refine ⟨?_, ?_⟩
  · intro hm_pos hm_lt u₀ hu₀
    exact hslow_diffusion ha hb hβ hm_pos hm_lt u₀ hu₀
  · intro hm_eq hχ u₀ hu₀
    exact hcritical ha hb hβ hm_eq hχ u₀ hu₀

/-- Generic existence-hypothesis closure for Paper 2 Theorem 1.3. -/
theorem Theorem_1_3.of_assumed_solutions_branch
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (hlocal :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2ClassicalSolution D p Tmax u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2BoundedBefore D Tmax u)
    (hglobal :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      1 ≤ p.m →
      ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
        ∃ u v : ℝ → D.Point → ℝ,
          IsPaper2GlobalClassicalSolution D p u v ∧
            InitialTrace D u₀ u ∧
            IsPaper2Bounded D u) :
    Theorem_1_3 D p C := by
  intro ha hb hm hcond
  refine ⟨?_, ?_⟩
  · intro u₀ hu₀
    exact hlocal ha hb hm hcond u₀ hu₀
  · intro hm_one u₀ hu₀
    exact hglobal ha hb hm hcond hm_one u₀ hu₀

/-! ### Concrete unit-point bounded domain

Single-point spatial domain `Unit`.  Every classical solution `u` is
characterised by `t ↦ u t ()`, which solves the logistic ODE
`û' = û (a - b û^α)` plus pointwise positivity, with the elliptic equation
forcing `v t () = (ν/μ) (u t ())^γ`.  The parabolic max principle reduces to
standard ODE analysis; we instantiate `ParabolicMaxPrincipleData` directly. -/

/-- Trivial Unit-point bounded domain.  Spatial derivatives all vanish; the
abstract `timeDeriv` is the real time derivative of the scalar profile;
classical regularity asks for differentiability of `t ↦ u t ()` and
continuity of `t ↦ v t ()`. -/
def unitPointDomain : BoundedDomainData where
  Point := Unit
  inside := Set.univ
  boundary := ∅
  volume := 1
  supNorm := fun f => |f ()|
  infValue := fun f => f ()
  integral := fun f => f ()
  gradNorm := fun _ _ => 0
  timeDeriv := fun u t _ => deriv (fun s : ℝ => u s ()) t
  laplacian := fun _ _ => 0
  chemotaxisDiv := fun _ _ _ _ => 0
  crossDiffusionEnergyTerm := fun _ _ _ _ => 0
  normalDeriv := fun _ _ => 0
  initialAdmissible := fun _ => True
  classicalRegularity := fun _ u v =>
    Differentiable ℝ (fun t : ℝ => u t ()) ∧ Continuous (fun t : ℝ => v t ())

/-- For the unit-point domain, the `ParabolicMaxPrincipleData` is witnessed
analytically: continuity comes from `Differentiable.continuous`, and the
nonpositive derivative above threshold comes from the logistic ODE
`û' = û (a - b û^α)`. -/
theorem unitPointDomain.parabolicMaxPrincipleData
    (p : CM2Params) : ParabolicMaxPrincipleData unitPointDomain p where
  supNorm_continuous_in_time := by
    intro T _hT u v hsol
    obtain ⟨_, ⟨hu_diff, _⟩, _, _, _, _⟩ := hsol
    exact (hu_diff.continuous.abs).continuousOn
  nonminimal_supNorm_hasDerivAt_nonpos := by
    intro _hχ ha hb T _hT u v hsol t ht_in_Ioo hgt
    obtain ⟨_, ⟨hu_diff, _⟩, hpos, hpde_u, _, _⟩ := hsol
    have hu_pos : 0 < u t () :=
      hpos t () ht_in_Ioo.1 ht_in_Ioo.2 trivial
    -- supNorm at t equals u t ()
    have hsup_eq : |u t ()| = u t () := abs_of_pos hu_pos
    -- HasDerivAt of (fun s ↦ u s ()) at t
    have hu_hasDerivAt :
        HasDerivAt (fun s : ℝ => u s ())
          (deriv (fun s : ℝ => u s ()) t) t :=
      (hu_diff t).hasDerivAt
    -- u positive in a neighborhood of t (continuity)
    have hu_cont : Continuous (fun s : ℝ => u s ()) := hu_diff.continuous
    have h_pos_nbhd : ∀ᶠ s in 𝓝 t, 0 < u s () :=
      continuousAt_const.eventually_lt hu_cont.continuousAt hu_pos
    -- On that neighborhood, |u s ()| = u s ()
    have h_eq_nbhd :
        (fun s : ℝ => |u s ()|) =ᶠ[𝓝 t] (fun s : ℝ => u s ()) := by
      filter_upwards [h_pos_nbhd] with s hs using abs_of_pos hs
    -- Transfer HasDerivAt to the absolute-value composition
    have habs_hasDerivAt :
        HasDerivAt (fun s : ℝ => |u s ()|)
          (deriv (fun s : ℝ => u s ()) t) t :=
      h_eq_nbhd.hasDerivAt_iff.mpr hu_hasDerivAt
    -- The PDE pins down the derivative value
    have hpde := hpde_u t () ht_in_Ioo.1 ht_in_Ioo.2 trivial
    -- For unitPointDomain: timeDeriv = deriv, laplacian = 0, chemotaxisDiv = 0
    have hpde' :
        deriv (fun s : ℝ => u s ()) t =
          u t () * (p.a - p.b * (u t ()) ^ p.α) := by
      simpa [unitPointDomain] using hpde
    -- Provide the derivative witness with the nonpositivity proof
    refine ⟨deriv (fun s : ℝ => u s ()) t, ?_, habs_hasDerivAt⟩
    rw [hpde']
    -- Show u t () * (p.a - p.b * (u t ()) ^ p.α) ≤ 0
    -- From hgt : (p.a / p.b) ^ (1 / p.α) < |u t ()|, with |u t ()| = u t ()
    have hgt' : (p.a / p.b) ^ (1 / p.α) < u t () := by
      have : (p.a / p.b) ^ (1 / p.α) < |u t ()| := hgt
      rwa [hsup_eq] at this
    -- Raise both sides to power α: a/b < (u t ())^α
    have hα_pos : 0 < p.α := p.hα
    have hα_ne : p.α ≠ 0 := ne_of_gt hα_pos
    have hab_nn : 0 ≤ p.a / p.b := div_nonneg ha.le hb.le
    have h_lhs : ((p.a / p.b) ^ (1 / p.α)) ^ p.α = p.a / p.b := by
      rw [← Real.rpow_mul hab_nn, one_div_mul_cancel hα_ne, Real.rpow_one]
    have h_uα :
        p.a / p.b < (u t ()) ^ p.α := by
      have hraw :=
        Real.rpow_lt_rpow (Real.rpow_nonneg hab_nn _) hgt' hα_pos
      rwa [h_lhs] at hraw
    have h_b_uα : p.a < p.b * (u t ()) ^ p.α := by
      have := mul_lt_mul_of_pos_left h_uα hb
      rwa [mul_div_cancel₀ _ (ne_of_gt hb)] at this
    have h_reaction_neg : p.a - p.b * (u t ()) ^ p.α < 0 := by linarith
    -- Product of positive and negative is nonpositive
    have h_prod : u t () * (p.a - p.b * (u t ()) ^ p.α) ≤ 0 :=
      le_of_lt (mul_neg_of_pos_of_neg hu_pos h_reaction_neg)
    exact h_prod
  minimal_supNorm_hasDerivAt_nonpos := by
    intro _hχ ha hb T _hT u v hsol t ht_in_Ioo
    obtain ⟨_, ⟨hu_diff, _⟩, hpos, hpde_u, _, _⟩ := hsol
    have hu_pos : 0 < u t () :=
      hpos t () ht_in_Ioo.1 ht_in_Ioo.2 trivial
    have hu_cont : Continuous (fun s : ℝ => u s ()) := hu_diff.continuous
    have h_pos_nbhd : ∀ᶠ s in 𝓝 t, 0 < u s () :=
      continuousAt_const.eventually_lt hu_cont.continuousAt hu_pos
    have h_eq_nbhd :
        (fun s : ℝ => |u s ()|) =ᶠ[𝓝 t] (fun s : ℝ => u s ()) := by
      filter_upwards [h_pos_nbhd] with s hs using abs_of_pos hs
    have hu_hasDerivAt :
        HasDerivAt (fun s : ℝ => u s ())
          (deriv (fun s : ℝ => u s ()) t) t :=
      (hu_diff t).hasDerivAt
    have habs_hasDerivAt :
        HasDerivAt (fun s : ℝ => |u s ()|)
          (deriv (fun s : ℝ => u s ()) t) t :=
      h_eq_nbhd.hasDerivAt_iff.mpr hu_hasDerivAt
    have hpde := hpde_u t () ht_in_Ioo.1 ht_in_Ioo.2 trivial
    have hpde' :
        deriv (fun s : ℝ => u s ()) t =
          u t () * (p.a - p.b * (u t ()) ^ p.α) := by
      simpa [unitPointDomain] using hpde
    refine ⟨deriv (fun s : ℝ => u s ()) t, ?_, habs_hasDerivAt⟩
    rw [hpde', ha, hb]
    ring_nf
    -- After substituting a = 0, b = 0: u t () * (0 - 0 * (u t ())^α) = 0 ≤ 0
    rfl

/-- **Paper 2 Lemma 3.1 holds unconditionally for the unit-point domain.**
Combining `unitPointDomain.parabolicMaxPrincipleData` with the conditional
bridge `Lemma_3_1_of_parabolicMaxPrinciple` closes the lemma.  Concrete
witness of the parabolic max principle structure. -/
theorem unitPointDomain.Lemma_3_1 (p : CM2Params) :
    Lemma_3_1 unitPointDomain p :=
  Lemma_3_1_of_parabolicMaxPrinciple
    (unitPointDomain.parabolicMaxPrincipleData p)

/-- Trivial `SemigroupEstimateData` on the unit-point domain.  All norms
identically zero; semigroup acts trivially.  Provides a concrete instance
where Proposition 2.1's elliptic Lᵖ comparison holds vacuously. -/
def trivialSemigroupData :
    SemigroupEstimateData unitPointDomain where
  lpNorm := fun _ _ => 0
  vectorLpNorm := fun _ _ => 0
  fractionalNorm := fun _ _ _ => 0
  semigroup := fun _ u => u
  divergenceSemigroup := fun _ _ _ => 0
  embeddingNorm := fun _ _ _ _ => 0

/-- Paper 2 Proposition 2.1 holds for the unit-point domain with the trivial
semigroup data: the elliptic comparison `S.lpNorm pExp (v t) ≤ (ν/μ) * …`
reduces to `0 ≤ 0`. -/
theorem trivialSemigroupData.Proposition_2_1 (p : CM2Params) :
    Proposition_2_1 unitPointDomain p trivialSemigroupData := by
  intro T _hT u v _hsol pExp _hpExp t _ht_pos _ht_lt
  simp [trivialSemigroupData]

/-- Paper 2 Lemma 4.1 holds for the unit-point domain: `D.gradNorm = 0`
makes the gradient integral vanish, so picking `Ceps := 1` gives the
trivial bound `(u t ())^pExp ≤ (u t ())^pExp`. -/
theorem unitPointDomain.Lemma_4_1 (p : CM2Params) :
    Lemma_4_1 unitPointDomain p := by
  intro u₀ _hu₀ T _hT u v _hsol _htrace eps _heps pExp _hpExp
  refine ⟨1, by norm_num, ?_⟩
  intro t _ht_pos _ht_lt
  simp [unitPointDomain]

/-- Paper 2 Proposition 2.5 holds for the unit-point domain: an `L^pExp`
bound on `(u t ())^pExp` gives a pointwise bound `u t () ≤ C^(1/pExp)`
hence a sup-norm bound. -/
theorem unitPointDomain.Proposition_2_5 (p : CM2Params) :
    Proposition_2_5 unitPointDomain p := by
  intro u₀ _hu₀ Tmax hTmax u v hsol _htrace pExp hpExp hlp
  obtain ⟨_, _, hu_pos, _, _, _⟩ := hsol
  obtain ⟨C, hC⟩ := hlp
  have hN_pos : 1 ≤ (p.N : ℝ) := by exact_mod_cast p.hN
  have hpExp_pos : 0 < pExp := by
    have h1 : (p.N : ℝ) ≤
        max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) := le_max_left _ _
    linarith
  have hpExp_ne : pExp ≠ 0 := ne_of_gt hpExp_pos
  have hT_half_pos : 0 < Tmax / 2 := by linarith
  have hT_half_lt : Tmax / 2 < Tmax := by linarith
  -- C ≥ 0: at some t ∈ (0, Tmax), (u t ())^pExp ≤ C and ≥ 0
  have hu_mid_pos : 0 < u (Tmax / 2) () :=
    hu_pos (Tmax / 2) () hT_half_pos hT_half_lt trivial
  have hC_nonneg : 0 ≤ C := by
    have := hC (Tmax / 2) hT_half_pos hT_half_lt
    simp [unitPointDomain] at this
    exact le_trans (Real.rpow_nonneg hu_mid_pos.le _) this
  refine ⟨C ^ (1 / pExp), ?_⟩
  intro t ht_pos ht_lt
  have hu_t_pos : 0 < u t () := hu_pos t () ht_pos ht_lt trivial
  show |u t ()| ≤ C ^ (1 / pExp)
  rw [abs_of_pos hu_t_pos]
  have hbd : (u t ()) ^ pExp ≤ C := by
    have := hC t ht_pos ht_lt
    simpa [unitPointDomain] using this
  have h_inv_nonneg : 0 ≤ 1 / pExp := by positivity
  have h_raised :
      ((u t ()) ^ pExp) ^ (1 / pExp) ≤ C ^ (1 / pExp) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hu_t_pos.le _) hbd h_inv_nonneg
  have h_simp : ((u t ()) ^ pExp) ^ (1 / pExp) = u t () := by
    rw [← Real.rpow_mul hu_t_pos.le, mul_one_div_cancel hpExp_ne, Real.rpow_one]
  -- Convert IsPaper2BoundedBefore conclusion
  show u t () ≤ C ^ (1 / pExp)
  linarith

/-- Paper 2 Proposition 2.2 holds for the unit-point domain: with
`D.gradNorm = 0`, the weighted gradient integrals all vanish so the
inequality reduces to `0 ≤ (nonneg)`. -/
theorem unitPointDomain.Proposition_2_2 (p : CM2Params) :
    Proposition_2_2 unitPointDomain p := by
  intro T _hT u v hsol pExp hpExp
  refine ⟨1, by norm_num, ?_⟩
  intro t ht_pos ht_lt
  obtain ⟨_, _, hupos, _, _, _⟩ := hsol
  have hu_pos : 0 < u t () := hupos t () ht_pos ht_lt trivial
  have h2p_ne : 2 * pExp ≠ 0 := by
    have : 0 < pExp := lt_trans zero_lt_one hpExp
    positivity
  have h2p_pos : 0 < 2 * pExp := by
    have : 0 < pExp := lt_trans zero_lt_one hpExp
    positivity
  have hβ_nonneg : 0 ≤ p.β := p.hβ
  have hΘ_nonneg : 0 ≤ Theta_beta p.β :=
    le_of_lt (Theta_beta_pos_of_nonneg hβ_nonneg)
  refine ⟨?_, ?_⟩
  · -- 0 ^ (2 * pExp) / (v t ())^pExp ≤ 1 * (u t ())^(p.γ * pExp)
    simp only [unitPointDomain, Real.zero_rpow h2p_ne, zero_div, one_mul]
    exact Real.rpow_nonneg hu_pos.le _
  · -- 0 ^ (2 * pExp) / (1 + v t ())^((1+β)*pExp) ≤ Theta^pExp * 1 * (u t ())^(γ*pExp)
    simp only [unitPointDomain, Real.zero_rpow h2p_ne, zero_div, mul_one]
    positivity

/-- Paper 2 Proposition 2.3 holds for the unit-point domain.  At the unit
point, the algebraic identity
`(v / (1+v)^(β/(p+1)))^(p+1) = v^(p+1) / (1+v)^β` lets `Ceps = 1` exactly
match the left-hand side, while the `ε` term is nonnegative because `u > 0`
and `1+v > 0`. -/
theorem unitPointDomain.Proposition_2_3 (p : CM2Params) :
    Proposition_2_3 unitPointDomain p := by
  intro T _hT u v hsol pExp hpExp eps heps
  refine ⟨1, by norm_num, ?_⟩
  intro t ht_pos ht_lt
  obtain ⟨_, _, hupos, _, hpde_v, _⟩ := hsol
  have hu_pos : 0 < u t () := hupos t () ht_pos ht_lt trivial
  have hpExp_pos : 0 < pExp :=
    lt_trans zero_lt_one
      (lt_of_le_of_lt (le_max_left 1 p.β) hpExp)
  have hp1_pos : 0 < pExp + 1 := by linarith
  have hp1_ne : pExp + 1 ≠ 0 := ne_of_gt hp1_pos
  -- v t () = (ν/μ) (u t ())^γ from the PDE for v
  have hpde_v_at := hpde_v t () ht_pos ht_lt trivial
  have h0 : (0 : ℝ) = 0 - p.μ * v t () + p.ν * (u t ()) ^ p.γ := by
    simpa [unitPointDomain] using hpde_v_at
  have hμ_pos : 0 < p.μ := p.hμ
  have hν_pos : 0 < p.ν := p.hν
  have huγ_pos : 0 < (u t ()) ^ p.γ := Real.rpow_pos_of_pos hu_pos _
  have hv_pos : 0 < v t () := by
    have hμv : p.μ * v t () = p.ν * (u t ()) ^ p.γ := by linarith
    have hprod_pos : 0 < p.μ * v t () := by
      rw [hμv]; exact mul_pos hν_pos huγ_pos
    exact (mul_pos_iff_of_pos_left hμ_pos).mp hprod_pos
  have h1V_pos : 0 < 1 + v t () := by linarith
  -- Goal at the unit point
  show (v t ()) ^ (pExp + 1) / (1 + v t ()) ^ p.β ≤
      eps * ((u t ()) ^ (p.γ * (pExp + 1)) / (1 + v t ()) ^ p.β) +
        1 * (v t () / (1 + v t ()) ^ (p.β / (pExp + 1))) ^ (pExp + 1)
  -- Identity for the last term
  have h1V_rpow_pos : 0 < (1 + v t ()) ^ (p.β / (pExp + 1)) :=
    Real.rpow_pos_of_pos h1V_pos _
  have hidentity :
      (v t () / (1 + v t ()) ^ (p.β / (pExp + 1))) ^ (pExp + 1) =
        (v t ()) ^ (pExp + 1) / (1 + v t ()) ^ p.β := by
    rw [Real.div_rpow hv_pos.le h1V_rpow_pos.le]
    congr 1
    rw [← Real.rpow_mul h1V_pos.le]
    congr 1
    field_simp
  rw [hidentity]
  -- Now: LHS ≤ ε * (nonneg) + 1 * LHS
  have hu_p_pos : 0 < (u t ()) ^ (p.γ * (pExp + 1)) :=
    Real.rpow_pos_of_pos hu_pos _
  have h1V_β_pos : 0 < (1 + v t ()) ^ p.β :=
    Real.rpow_pos_of_pos h1V_pos _
  have h_eps_term_nonneg :
      0 ≤ eps * ((u t ()) ^ (p.γ * (pExp + 1)) / (1 + v t ()) ^ p.β) := by
    apply mul_nonneg heps.le
    exact div_nonneg hu_p_pos.le h1V_β_pos.le
  linarith

/-- Paper 2 Proposition 2.4 holds for the unit-point domain.  Two branches:
* `a = 0, b = 0`: `u'(s) = 0` on `(0, T)`, so `u` is constant on the
  preconnected open set `(0, T)`; combined with the initial trace
  `u(s) → u₀()` as `s → 0+`, the constant equals `u₀()`, giving
  `MassConservedBefore` at every interior time.
* `0 < a, 0 < b`: above the threshold `K := (a/b)^(1/α)` the ODE
  `u'(s) = u(s)(a - b u(s)^α)` has negative derivative.  By
  `threshold_persists_below_of_hasDerivAt_nonpos`, exceeding `K` at `t`
  propagates back through `(0, t]`, on which `u` is antitone; the
  initial trace then forces `u(t) ≤ u₀()`. -/
theorem unitPointDomain.Proposition_2_4 (p : CM2Params) :
    Proposition_2_4 unitPointDomain p := by
  intro u₀ _hu₀ T _hT u v hsol htrace
  obtain ⟨_, ⟨hu_diff, _⟩, hupos, hpde_u, _, _⟩ := hsol
  refine ⟨?_, ?_⟩
  · -- Case 1: a = b = 0
    intro ha hb t ht_pos ht_T
    have hderiv_zero :
        ∀ s ∈ Set.Ioo (0 : ℝ) T, deriv (fun s' : ℝ => u s' ()) s = 0 := by
      intro s hs
      have h := hpde_u s () hs.1 hs.2 trivial
      have h' :
          deriv (fun s' : ℝ => u s' ()) s =
            u s () * (p.a - p.b * (u s ()) ^ p.α) := by
        simpa [unitPointDomain] using h
      rw [h', ha, hb]; ring
    have hconst :
        ∀ s₁ ∈ Set.Ioo (0 : ℝ) T, ∀ s₂ ∈ Set.Ioo (0 : ℝ) T,
          u s₁ () = u s₂ () := fun s₁ hs₁ s₂ hs₂ =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hu_diff.differentiableOn hderiv_zero hs₁ hs₂
    have h_abs : ∀ ε > 0, |u t () - u₀ ()| < ε := by
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := htrace ε hε
      set s := min (δ / 2) (T / 2) with hs_def
      have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
      have hs_lt_δ : s < δ :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hs_lt_T : s < T :=
        lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have h1 : u t () = u s () :=
        hconst t ⟨ht_pos, ht_T⟩ s ⟨hs_pos, hs_lt_T⟩
      have h2 : |u s () - u₀ ()| < ε := by
        have := hδ s hs_pos hs_lt_δ
        simpa [unitPointDomain] using this
      rw [h1]; exact h2
    have hu_eq : u t () = u₀ () := by
      have h_zero : u t () - u₀ () = 0 := by
        by_contra h_ne
        have hpos : 0 < |u t () - u₀ ()| := abs_pos.mpr h_ne
        exact absurd (h_abs (|u t () - u₀ ()|) hpos) (lt_irrefl _)
      linarith
    show unitPointDomain.integral (u t) = unitPointDomain.integral u₀
    simpa [unitPointDomain] using hu_eq
  · -- Case 2: 0 < a, 0 < b
    intro ha hb t ht_pos ht_T
    show unitPointDomain.integral (u t) ≤
        max (unitPointDomain.integral u₀)
          ((p.a / p.b) ^ (1 / p.α) * unitPointDomain.volume)
    suffices h : u t () ≤ max (u₀ ()) ((p.a / p.b) ^ (1 / p.α)) by
      simpa [unitPointDomain, mul_one] using h
    set K := (p.a / p.b) ^ (1 / p.α) with hK_def
    by_cases hle : u t () ≤ K
    · exact le_trans hle (le_max_right _ _)
    push_neg at hle
    let M : ℝ → ℝ := fun s => u s ()
    have hM_cont : ContinuousOn M (Set.Ioo (0 : ℝ) T) :=
      hu_diff.continuous.continuousOn
    have hM_deriv :
        ∀ s ∈ Set.Ioo (0 : ℝ) T, K < M s →
          ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt M d s := by
      intro s hs hM_gt
      have hu_pos : 0 < u s () := hupos s () hs.1 hs.2 trivial
      have hα_pos : 0 < p.α := p.hα
      have hα_ne : p.α ≠ 0 := ne_of_gt hα_pos
      have hab_nn : 0 ≤ p.a / p.b := div_nonneg ha.le hb.le
      have h_lhs : (K ^ p.α : ℝ) = p.a / p.b := by
        rw [hK_def, ← Real.rpow_mul hab_nn, one_div_mul_cancel hα_ne,
          Real.rpow_one]
      have h_uα : p.a / p.b < (u s ()) ^ p.α := by
        have := Real.rpow_lt_rpow (Real.rpow_nonneg hab_nn _) hM_gt hα_pos
        rw [h_lhs] at this; exact this
      have h_b_uα : p.a < p.b * (u s ()) ^ p.α := by
        have hcalc := mul_lt_mul_of_pos_left h_uα hb
        rwa [mul_div_cancel₀ _ (ne_of_gt hb)] at hcalc
      have h_reaction_neg : p.a - p.b * (u s ()) ^ p.α < 0 := by linarith
      have h_prod_nonpos : u s () * (p.a - p.b * (u s ()) ^ p.α) ≤ 0 :=
        le_of_lt (mul_neg_of_pos_of_neg hu_pos h_reaction_neg)
      have hpde := hpde_u s () hs.1 hs.2 trivial
      have hpde' :
          deriv (fun s' : ℝ => u s' ()) s =
            u s () * (p.a - p.b * (u s ()) ^ p.α) := by
        simpa [unitPointDomain] using hpde
      refine ⟨deriv (fun s' : ℝ => u s' ()) s, ?_, ?_⟩
      · rw [hpde']; exact h_prod_nonpos
      · exact (hu_diff s).hasDerivAt
    have hAbove : ∀ s ∈ Set.Ioc (0 : ℝ) t, K < M s :=
      threshold_persists_below_of_hasDerivAt_nonpos
        ht_pos ht_T hM_cont hM_deriv hle
    have hM_antitone : ∀ s ∈ Set.Ioc (0 : ℝ) t, M t ≤ M s := by
      intro s hs
      obtain ⟨hs_pos, hs_le⟩ := hs
      have hIcc_sub_Ioo : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T :=
        fun s' ⟨h1, h2⟩ =>
          ⟨lt_of_lt_of_le hs_pos h1, lt_of_le_of_lt h2 ht_T⟩
      have hIcc_sub_Ioc : Set.Icc s t ⊆ Set.Ioc (0 : ℝ) t :=
        fun s' ⟨h1, h2⟩ => ⟨lt_of_lt_of_le hs_pos h1, h2⟩
      have hM_cont_Icc : ContinuousOn M (Set.Icc s t) :=
        hM_cont.mono hIcc_sub_Ioo
      have hM_deriv_Ioo :
          ∀ s' ∈ Set.Ioo s t,
            DifferentiableAt ℝ M s' ∧ deriv M s' ≤ 0 := by
        intro s' hs'
        have hs'_in_Ioo : s' ∈ Set.Ioo (0 : ℝ) T :=
          hIcc_sub_Ioo ⟨hs'.1.le, hs'.2.le⟩
        have hs'_in_Ioc : s' ∈ Set.Ioc (0 : ℝ) t :=
          hIcc_sub_Ioc ⟨hs'.1.le, hs'.2.le⟩
        have hs'_gt : K < M s' := hAbove s' hs'_in_Ioc
        obtain ⟨d, hd_nonpos, hd⟩ := hM_deriv s' hs'_in_Ioo hs'_gt
        exact ⟨hd.differentiableAt, by rw [hd.deriv]; exact hd_nonpos⟩
      have hDiff_Ioo : DifferentiableOn ℝ M (Set.Ioo s t) :=
        fun s' hs' => (hM_deriv_Ioo s' hs').1.differentiableWithinAt
      have hDeriv_nonpos :
          ∀ s' ∈ interior (Set.Icc s t), deriv M s' ≤ 0 := by
        intro s' hs'
        rw [interior_Icc] at hs'
        exact (hM_deriv_Ioo s' hs').2
      have hAntitone : AntitoneOn M (Set.Icc s t) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hM_cont_Icc
        · rw [interior_Icc]; exact hDiff_Ioo
        · exact hDeriv_nonpos
      exact hAntitone (Set.left_mem_Icc.mpr hs_le)
        (Set.right_mem_Icc.mpr hs_le) hs_le
    have hM_t_le_u₀ : M t ≤ u₀ () := by
      have h_lt_all : ∀ ε > 0, M t < u₀ () + ε := by
        intro ε hε
        obtain ⟨δ, hδ_pos, hδ⟩ := htrace ε hε
        set s := min (δ / 2) (t / 2) with hs_def
        have hs_pos : 0 < s :=
          lt_min (by linarith) (by linarith)
        have hs_lt_δ : s < δ :=
          lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hs_le_t : s ≤ t :=
          le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith))
        have h1 : M t ≤ M s := hM_antitone s ⟨hs_pos, hs_le_t⟩
        have h2 : |u s () - u₀ ()| < ε := by
          have := hδ s hs_pos hs_lt_δ
          simpa [unitPointDomain] using this
        have h3 : u s () < u₀ () + ε := by
          have := (abs_sub_lt_iff.mp h2).1
          linarith
        calc M t ≤ M s := h1
          _ = u s () := rfl
          _ < u₀ () + ε := h3
      by_contra h_gt
      push_neg at h_gt
      have := h_lt_all (M t - u₀ ()) (by linarith)
      linarith
    calc u t () = M t := rfl
      _ ≤ u₀ () := hM_t_le_u₀
      _ ≤ max (u₀ ()) K := le_max_left _ _

/-- Paper 2 Theorem 1.1 holds for the unit-point domain in the *minimal*
parameter regime `p.a = 0 ∧ p.b = 0`.  The nonminimal branch
`0 < p.a → 0 < p.b → …` is vacuous; for the minimal branch the constant
solution `u(t) = u₀, v(t) = (ν/μ) · u₀()^γ` is a classical solution on every
finite horizon. -/
theorem unitPointDomain.Theorem_1_1_minimal_only
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) :
    Theorem_1_1 unitPointDomain p := by
  intro _hχ
  refine ⟨?_, ?_⟩
  · -- Nonminimal branch is vacuous since p.a = 0
    intro ha' _ _ _
    exact absurd ha' (by rw [ha]; exact lt_irrefl 0)
  · -- Minimal branch: a = b = 0
    intro _ _ u₀ hu₀
    set ustar : ℝ := (p.ν / p.μ) * (u₀ ()) ^ p.γ with hustar_def
    refine ⟨1, by norm_num, fun _ => u₀, fun _ _ => ustar, ?_, ?_, ?_, ?_⟩
    · -- IsPaper2ClassicalSolution unitPointDomain p 1 (fun _ => u₀) (fun _ _ => ustar)
      refine ⟨by norm_num, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · -- Differentiable ℝ (fun t : ℝ => u₀ ())
        exact differentiable_const _
      · -- Continuous (fun t : ℝ => ustar)
        exact continuous_const
      · -- u_pos
        intro t x _ _ _
        exact hu₀.pos trivial
      · -- pde_u
        intro t x _ _ _
        show deriv (fun s : ℝ => u₀ ()) t = 0 - p.χ₀ * 0 +
          u₀ x * (p.a - p.b * (u₀ x) ^ p.α)
        rw [deriv_const]
        rw [ha, hb]; ring
      · -- pde_v: 0 = D.laplacian (v t) x - p.μ * v t x + p.ν * (u t x)^p.γ
        intro t x _ _ _
        show (0 : ℝ) = 0 - p.μ * ustar + p.ν * (u₀ x) ^ p.γ
        -- For unit point, x = (), so u₀ x = u₀ ()
        have hxeq : x = () := rfl
        rw [hxeq, hustar_def]
        have hμ_ne : p.μ ≠ 0 := ne_of_gt p.hμ
        field_simp
        ring
      · -- Neumann (boundary = ∅)
        intro t x _ _ hx
        exact absurd hx (by intro h; exact h)
    · -- InitialTrace
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro t _ _
      show unitPointDomain.supNorm (fun x => u₀ x - u₀ x) < ε
      have : (fun x : unitPointDomain.Point => u₀ x - u₀ x) = fun _ => 0 := by
        funext x; ring
      rw [this]
      show |(0 : ℝ)| < ε
      simpa using hε
    · -- supNorm bound (minimal branch: just ≤ supNorm u₀)
      intro t _ _
      show unitPointDomain.supNorm u₀ ≤ unitPointDomain.supNorm u₀
      exact le_refl _
    · -- Global if 1 ≤ p.m
      intro _ T hT
      refine ⟨hT, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · exact differentiable_const _
      · exact continuous_const
      · intro t x _ _ _
        exact hu₀.pos trivial
      · intro t x _ _ _
        show deriv (fun s : ℝ => u₀ ()) t = 0 - p.χ₀ * 0 +
          u₀ x * (p.a - p.b * (u₀ x) ^ p.α)
        rw [deriv_const]
        rw [ha, hb]; ring
      · intro t x _ _ _
        show (0 : ℝ) = 0 - p.μ * ustar + p.ν * (u₀ x) ^ p.γ
        have hxeq : x = () := rfl
        rw [hxeq, hustar_def]
        have hμ_ne : p.μ ≠ 0 := ne_of_gt p.hμ
        field_simp
        ring
      · intro t x _ _ hx
        exact absurd hx (by intro h; exact h)

/-- Paper 2 unit-point long-time attractor bridge.

`ShenWork.PDE.UnitPointLogisticODE` constructs the concrete Bernoulli-logistic
global solution and proves this exact package.  Since that file imports the
statement layer, this bridge is stated with the explicit package as an input
rather than importing the ODE file back here. -/
theorem unitPointDomain.Theorem_X_X_long_time_attractor
    (p : CM2Params)
    (hexplicit :
      0 < p.a → 0 < p.b →
        ∀ u₀ : unitPointDomain.Point → ℝ,
          PositiveInitialDatum unitPointDomain u₀ →
            ∃ u v : ℝ → unitPointDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution unitPointDomain p u v ∧
              InitialTrace unitPointDomain u₀ u ∧
              (∀ t, 0 ≤ t →
                unitPointDomain.supNorm (u t) ≤
                  max (unitPointDomain.supNorm u₀)
                    ((p.a / p.b) ^ (1 / p.α))) ∧
              Tendsto (fun t : ℝ => u t ())
                atTop (𝓝 ((p.a / p.b) ^ (1 / p.α)))) :
    0 < p.a → 0 < p.b →
      ∀ u₀ : unitPointDomain.Point → ℝ,
        PositiveInitialDatum unitPointDomain u₀ →
          ∃ u v : ℝ → unitPointDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution unitPointDomain p u v ∧
            InitialTrace unitPointDomain u₀ u ∧
            (∀ t, 0 ≤ t →
              unitPointDomain.supNorm (u t) ≤
                max (unitPointDomain.supNorm u₀)
                  ((p.a / p.b) ^ (1 / p.α))) ∧
            Tendsto (fun t : ℝ => u t ())
              atTop (𝓝 ((p.a / p.b) ^ (1 / p.α))) := by
  intro ha hb u₀ hu₀
  exact hexplicit ha hb u₀ hu₀

/-- Paper 2 unit-point exponential convergence bridge.

The concrete rate package is proved for the explicit Bernoulli-logistic
solution in `ShenWork.PDE.UnitPointLogisticODE`.  The rate is stated in the
Bernoulli coordinate `u^{-α}`, where the decay is exactly exponential with
rate `αa`. -/
theorem unitPointDomain.Theorem_X_X_exponential_convergence
    (p : CM2Params)
    (hexplicit :
      0 < p.a → 0 < p.b →
        ∀ u₀ : unitPointDomain.Point → ℝ,
          PositiveInitialDatum unitPointDomain u₀ →
            ∃ u v : ℝ → unitPointDomain.Point → ℝ,
              IsPaper2GlobalClassicalSolution unitPointDomain p u v ∧
              InitialTrace unitPointDomain u₀ u ∧
              (∀ t, 0 ≤ t →
                unitPointDomain.supNorm (u t) ≤
                  max (unitPointDomain.supNorm u₀)
                    ((p.a / p.b) ^ (1 / p.α))) ∧
              Tendsto (fun t : ℝ => u t ())
                atTop (𝓝 ((p.a / p.b) ^ (1 / p.α))) ∧
              (∀ t, 0 ≤ t →
                |(u t ()) ^ (-p.α) - p.b / p.a| =
                  |(u₀ ()) ^ (-p.α) - p.b / p.a| *
                    Real.exp (-(p.α * p.a) * t))) :
    0 < p.a → 0 < p.b →
      ∀ u₀ : unitPointDomain.Point → ℝ,
        PositiveInitialDatum unitPointDomain u₀ →
          ∃ u v : ℝ → unitPointDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution unitPointDomain p u v ∧
            InitialTrace unitPointDomain u₀ u ∧
            (∀ t, 0 ≤ t →
              unitPointDomain.supNorm (u t) ≤
                max (unitPointDomain.supNorm u₀)
                  ((p.a / p.b) ^ (1 / p.α))) ∧
            Tendsto (fun t : ℝ => u t ())
              atTop (𝓝 ((p.a / p.b) ^ (1 / p.α))) ∧
            (∀ t, 0 ≤ t →
              |(u t ()) ^ (-p.α) - p.b / p.a| =
                |(u₀ ()) ^ (-p.α) - p.b / p.a| *
                  Real.exp (-(p.α * p.a) * t)) := by
  intro ha hb u₀ hu₀
  exact hexplicit ha hb u₀ hu₀

/-- Nonminimal unit-point logistic package exposed at the statement layer.

The concrete witness is `unitPointLogistic_globalExistence_with_attractor` in
`ShenWork.PDE.UnitPointLogisticODE`; this file cannot import it because that
ODE file imports the statement layer. -/
def UnitPointLogisticNonminimalPackage (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b →
    ∀ u₀ : unitPointDomain.Point → ℝ,
      PositiveInitialDatum unitPointDomain u₀ →
        ∃ u v : ℝ → unitPointDomain.Point → ℝ,
          IsPaper2GlobalClassicalSolution unitPointDomain p u v ∧
          InitialTrace unitPointDomain u₀ u ∧
          (∀ t, 0 ≤ t →
            unitPointDomain.supNorm (u t) ≤
              max (unitPointDomain.supNorm u₀)
                ((p.a / p.b) ^ (1 / p.α))) ∧
          Tendsto (fun t : ℝ => u t ())
            atTop (𝓝 ((p.a / p.b) ^ (1 / p.α)))

/-- Statement-layer closure of Paper 2 Theorem 1.1 on the unit-point domain.
The minimal branch is closed in this file; the nonminimal branch is routed
through the explicit Bernoulli-logistic package from
`ShenWork.PDE.UnitPointLogisticODE`. -/
theorem unitPointDomain.Theorem_1_1_from_logistic_nonminimal
    (p : CM2Params)
    (hlogistic : UnitPointLogisticNonminimalPackage p) :
    Theorem_1_1 unitPointDomain p := by
  intro hχ
  refine ⟨?_, ?_⟩
  · intro ha hb u₀ hu₀
    rcases hlogistic ha hb u₀ hu₀ with
      ⟨u, v, hglobal, htrace, hbound, _hlim⟩
    refine ⟨1, by norm_num, u, v, ?_, htrace, ?_, ?_⟩
    · exact hglobal.classical (T := 1) (by norm_num)
    · intro t ht_pos _ht_lt
      exact hbound t ht_pos.le
    · intro _hm
      exact hglobal
  · intro ha hb u₀ hu₀
    exact ((unitPointDomain.Theorem_1_1_minimal_only p ha hb) hχ).2
      ha hb u₀ hu₀

/-- Paper 2 Corollary 2.1 holds for the unit-point domain.  The classical
solution forces `u t () > 0` (from `u_pos`), so the abstract `Lᵖ` bound at
`p0` (which for the unit-point reduces to `(u t ())^p0 ≤ C₀`) implies a
direct sup bound `u t () ≤ C₀^(1/p0)` by raising to the `1/p0`-th power.
Then for any `pExp > 1` we get `(u t ())^pExp ≤ (C₀^(1/p0))^pExp`, which
is `LpPowerBoundedBefore` at `pExp`. -/
theorem unitPointDomain.Corollary_2_1 (p : CM2Params) :
    Corollary_2_1 unitPointDomain p := by
  intro T _hT u v hsol hbootstrap pExp hpExp
  obtain ⟨_, _, hupos, _, _, _⟩ := hsol
  obtain ⟨rho, _hrho, _hCDB, p0, hp0_gt, hLp0⟩ := hbootstrap
  obtain ⟨C₀, hC₀⟩ := hLp0
  have hp0_pos : 0 < p0 :=
    lt_trans zero_lt_one
      (lt_of_le_of_lt (le_max_left 1 _) hp0_gt)
  refine ⟨(max C₀ 1) ^ (pExp / p0), ?_⟩
  intro t ht_pos ht_lt
  have hu_pos : 0 < u t () := hupos t () ht_pos ht_lt trivial
  have hbd : (u t ()) ^ p0 ≤ C₀ := by
    have h := hC₀ t ht_pos ht_lt
    have hint : unitPointDomain.integral (fun x => (u t x) ^ p0) =
        (u t ()) ^ p0 := rfl
    rw [hint] at h
    exact h
  have hC_max_pos : 0 < max C₀ 1 :=
    lt_max_of_lt_right zero_lt_one
  -- u t () ^ p0 ≤ max C₀ 1
  have hbd' : (u t ()) ^ p0 ≤ max C₀ 1 := le_trans hbd (le_max_left _ _)
  -- Raise both sides to the (1/p0)-th power: u t () ≤ (max C₀ 1)^(1/p0)
  have h1p0_pos : 0 < 1 / p0 := by positivity
  have hle_rpow :
      ((u t ()) ^ p0) ^ (1 / p0) ≤ (max C₀ 1) ^ (1 / p0) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hu_pos.le p0) hbd' h1p0_pos.le
  have h_simp : ((u t ()) ^ p0) ^ (1 / p0) = u t () := by
    rw [← Real.rpow_mul hu_pos.le, mul_one_div_cancel (ne_of_gt hp0_pos),
      Real.rpow_one]
  rw [h_simp] at hle_rpow
  -- Now raise to pExp: (u t ())^pExp ≤ ((max C₀ 1)^(1/p0))^pExp
  have hpExp_pos : 0 < pExp := lt_trans zero_lt_one hpExp
  have hM_nn : 0 ≤ (max C₀ 1) ^ (1 / p0) :=
    Real.rpow_nonneg hC_max_pos.le _
  have hle_pExp :
      (u t ()) ^ pExp ≤ ((max C₀ 1) ^ (1 / p0)) ^ pExp :=
    Real.rpow_le_rpow hu_pos.le hle_rpow hpExp_pos.le
  -- Combine: ((max C₀ 1)^(1/p0))^pExp = (max C₀ 1)^(pExp/p0)
  have hM_combine :
      ((max C₀ 1) ^ (1 / p0)) ^ pExp = (max C₀ 1) ^ (pExp / p0) := by
    rw [← Real.rpow_mul hC_max_pos.le, one_div, inv_mul_eq_div]
  rw [hM_combine] at hle_pExp
  -- Reduce the integral form back
  have hint : unitPointDomain.integral (fun x => (u t x) ^ pExp) =
      (u t ()) ^ pExp := rfl
  rw [hint]
  exact hle_pExp

/-- Paper 2 Theorem 1.3 holds vacuously on the unit-point domain when
`p.a = 0` (or `p.b = 0`).  The whole theorem is conditional on
`0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition → ...`, so any of
those failing kills the implication. -/
theorem unitPointDomain.Theorem_1_3_vacuous_when_a_zero
    (p : CM2Params) (ha : p.a = 0) (C : Paper2Constants p) :
    Theorem_1_3 unitPointDomain p C := by
  intro ha' _ _ _
  exact absurd ha' (by rw [ha]; exact lt_irrefl 0)

/-- Paper 2 Theorem 1.3 holds vacuously on the unit-point domain when
`p.b = 0`. -/
theorem unitPointDomain.Theorem_1_3_vacuous_when_b_zero
    (p : CM2Params) (hb : p.b = 0) (C : Paper2Constants p) :
    Theorem_1_3 unitPointDomain p C := by
  intro _ hb' _ _
  exact absurd hb' (by rw [hb]; exact lt_irrefl 0)

/-- Paper 2 Theorem 1.2 holds for the unit-point domain in the *minimal*
parameter regime `p.a = 0 ∧ p.b = 0`.  In both branches (slow-diffusion
`0 < p.m < 1` and critical `p.m = 1`) the constant solution
`u(t) ≡ u₀, v(t) ≡ (ν/μ) u₀()^γ` works and the integral/sup-norm
boundedness conditions hold with `M := |u₀()|`. -/
theorem unitPointDomain.Theorem_1_2_minimal_only
    (p : CM2Params) (ha : p.a = 0) (hb : p.b = 0) :
    Theorem_1_2 unitPointDomain p := by
  intro _ha_nn _hb_nn _hβ
  -- Build a shared constant-solution closure
  refine ⟨?_, ?_⟩
  · -- Slow-diffusion branch: ∃ Tmax > 0, local bounded
    intro _hm_pos _hm_lt u₀ hu₀
    set ustar : ℝ := (p.ν / p.μ) * (u₀ ()) ^ p.γ with hustar_def
    refine ⟨1, by norm_num, fun _ => u₀, fun _ _ => ustar, ?_, ?_, ?_⟩
    · -- classical solution on (0, 1)
      refine ⟨by norm_num, ⟨differentiable_const _, continuous_const⟩,
        ?_, ?_, ?_, ?_⟩
      · intro t x _ _ _; exact hu₀.pos trivial
      · intro t x _ _ _
        show deriv (fun s : ℝ => u₀ ()) t =
          0 - p.χ₀ * 0 + u₀ x * (p.a - p.b * (u₀ x) ^ p.α)
        rw [deriv_const, ha, hb]; ring
      · intro t x _ _ _
        show (0 : ℝ) = 0 - p.μ * ustar + p.ν * (u₀ x) ^ p.γ
        have hxeq : x = () := rfl
        rw [hxeq, hustar_def]
        have hμ_ne : p.μ ≠ 0 := ne_of_gt p.hμ
        field_simp; ring
      · intro t x _ _ hx
        exact absurd hx (by intro h; exact h)
    · -- InitialTrace
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro t _ _
      show unitPointDomain.supNorm (fun x => u₀ x - u₀ x) < ε
      have hzero : (fun x : unitPointDomain.Point => u₀ x - u₀ x) = fun _ => 0 := by
        funext x; ring
      rw [hzero]
      show |(0 : ℝ)| < ε
      rw [abs_zero]; exact hε
    · -- IsPaper2BoundedBefore
      refine ⟨unitPointDomain.supNorm u₀, ?_⟩
      intro t _ _; exact le_refl _
  · -- Critical branch p.m = 1: global + bounded
    intro _hm_eq _hχ u₀ hu₀
    set ustar : ℝ := (p.ν / p.μ) * (u₀ ()) ^ p.γ with hustar_def
    refine ⟨fun _ => u₀, fun _ _ => ustar, ?_, ?_, ?_⟩
    · -- IsPaper2GlobalClassicalSolution
      intro T hT
      refine ⟨hT, ⟨differentiable_const _, continuous_const⟩,
        ?_, ?_, ?_, ?_⟩
      · intro t x _ _ _; exact hu₀.pos trivial
      · intro t x _ _ _
        show deriv (fun s : ℝ => u₀ ()) t =
          0 - p.χ₀ * 0 + u₀ x * (p.a - p.b * (u₀ x) ^ p.α)
        rw [deriv_const, ha, hb]; ring
      · intro t x _ _ _
        show (0 : ℝ) = 0 - p.μ * ustar + p.ν * (u₀ x) ^ p.γ
        have hxeq : x = () := rfl
        rw [hxeq, hustar_def]
        have hμ_ne : p.μ ≠ 0 := ne_of_gt p.hμ
        field_simp; ring
      · intro t x _ _ hx
        exact absurd hx (by intro h; exact h)
    · -- InitialTrace
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro t _ _
      show unitPointDomain.supNorm (fun x => u₀ x - u₀ x) < ε
      have hzero : (fun x : unitPointDomain.Point => u₀ x - u₀ x) = fun _ => 0 := by
        funext x; ring
      rw [hzero]
      show |(0 : ℝ)| < ε
      rw [abs_zero]; exact hε
    · -- IsPaper2Bounded
      refine ⟨unitPointDomain.supNorm u₀, ?_⟩
      exact Filter.Eventually.of_forall fun _ => le_refl _

/-- Paper 2 Theorem 1.3 is vacuous on the unit-point domain when
`p.m ≤ 0` (the hypothesis is `0 < p.m`). -/
theorem unitPointDomain.Theorem_1_3_vacuous_when_m_le_zero
    (p : CM2Params) (hm : p.m ≤ 0) (C : Paper2Constants p) :
    Theorem_1_3 unitPointDomain p C := by
  intro _ _ hm' _; exact absurd hm' (not_lt.mpr hm)

/-- Paper 2 Theorem 1.2 is vacuous on the unit-point domain when
`p.β < 1` (the hypothesis is `1 ≤ p.β`). -/
theorem unitPointDomain.Theorem_1_2_vacuous_when_beta_lt_one
    (p : CM2Params) (hβ : p.β < 1) :
    Theorem_1_2 unitPointDomain p := by
  intro _ _ hβ'; exact absurd hβ' (not_le.mpr hβ)

/-- Paper 2 Theorem 1.1 is vacuous on the unit-point domain when
`0 < p.χ₀` (the hypothesis is `p.χ₀ ≤ 0`). -/
theorem unitPointDomain.Theorem_1_1_vacuous_when_chi_pos
    (p : CM2Params) (hχ : 0 < p.χ₀) :
    Theorem_1_1 unitPointDomain p := by
  intro hχ'; exact absurd hχ' (not_le.mpr hχ)

/-- Paper 2 Lemma 2.7 does NOT hold unconditionally on `unitPointDomain`:
the differential inequality alone cannot prevent the Lp-power from blowing
up near `t = 0`.  For example, `u(t,()) = t⁻¹` with `pExp = 2`,
`C₁ = C₂ = C₃ = 0`, `C₄ = 1`, `α = ε = 1`, `T = 1` satisfies the
differential inequality on `(0,1)` yet `(u t ())² = t⁻²` is unbounded.

The corrected version adds continuity of the Lp-power map on the compact
interval `[0, T]`, from which the extreme value theorem gives a uniform
bound. -/
theorem unitPointDomain.Lemma_2_7_from_continuous_bound
    (u : ℝ → unitPointDomain.Point → ℝ) (T pExp C1 C2 C3 C4 eps alpha : ℝ)
    (hT : 0 < T) (_hpExp : 1 < pExp)
    (_hC1 : 0 ≤ C1) (_hC2 : 0 ≤ C2) (_hC3 : 0 ≤ C3) (_hC4 : 0 < C4)
    (_heps : 0 < eps) (_heps_le : eps ≤ alpha)
    (hcont : ContinuousOn (fun t => (u t ()) ^ pExp) (Set.Icc 0 T))
    (_hineq : ∀ t, 0 < t → t < T →
      deriv (fun τ => unitPointDomain.integral (fun x => (u τ x) ^ pExp)) t +
          C3 * unitPointDomain.integral (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
        C1 + C2 * unitPointDomain.integral (fun x => (u t x) ^ pExp) -
          C4 * unitPointDomain.integral (fun x => (u t x) ^ (pExp + alpha))) :
    LpPowerBoundedBefore unitPointDomain pExp T u := by
  -- On unitPointDomain, integral f = f (), so the conclusion asks for
  -- ∃ C, ∀ t ∈ (0,T), (u t ()) ^ pExp ≤ C.
  -- ContinuousOn on compact [0, T] gives the bound via the extreme value theorem.
  have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, Set.left_mem_Icc.mpr hT.le⟩
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨(u t₀ ()) ^ pExp, ?_⟩
  intro t ht_pos ht_lt
  have ht_mem : t ∈ Set.Icc (0 : ℝ) T := ⟨ht_pos.le, ht_lt.le⟩
  change unitPointDomain.integral (fun x => (u t x) ^ pExp) ≤ (u t₀ ()) ^ pExp
  change (fun t => (u t ()) ^ pExp) t ≤ (fun t => (u t ()) ^ pExp) t₀
  exact hmax ht_mem

/-- Paper 2 Proposition 1.1 is **not provable** on the unit-point domain.

On a zero-dimensional domain the PDE collapses to the logistic ODE.  For
`a = 0`, `b = 0` the unique classical solution is constant `u ≡ u₀`.  A
constant positive function is neither unbounded nor vanishing on any finite
time horizon, so `FiniteHorizonAlternative` is unsatisfiable. -/
theorem unitPointDomain.not_Proposition_1_1 :
    ¬ Proposition_1_1 unitPointDomain proposition11CounterParams := by
  intro h
  -- Use initial datum u₀ ≡ 1
  let u₀ : unitPointDomain.Point → ℝ := fun _ => 1
  have hu₀ : PositiveInitialDatum unitPointDomain u₀ :=
    ⟨trivial, fun _ _ => one_pos⟩
  rcases h u₀ hu₀ with ⟨Tmax, hTmax, u, v, hsol, htrace, halt, _⟩
  -- The PDE forces u'(t) = 0 on (0, Tmax)
  have hpde_zero : ∀ t, t ∈ Set.Ioo (0 : ℝ) Tmax →
      deriv (fun τ => u τ ()) t = 0 := by
    intro t ⟨ht0, htT⟩
    have := hsol.pde_u ht0 htT (Set.mem_univ ())
    simp only [unitPointDomain, proposition11CounterParams] at this
    linarith
  -- u is differentiable on ℝ (from classicalRegularity)
  have hu_diff : Differentiable ℝ (fun t : ℝ => u t ()) := hsol.regularity.1
  -- On (0, Tmax), deriv = 0, so u is constant there
  have hconst : ∀ s₁ s₂, s₁ ∈ Set.Ioo (0 : ℝ) Tmax → s₂ ∈ Set.Ioo (0 : ℝ) Tmax →
      u s₁ () = u s₂ () := by
    intro s₁ s₂ hs₁ hs₂
    exact IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      hu_diff.differentiableOn (fun x hx => hpde_zero x hx) hs₁ hs₂
  -- From InitialTrace, u → u₀ = 1 as t → 0+, so the constant equals 1
  have hone : ∀ t, 0 < t → t < Tmax → u t () = 1 := by
    intro t ht0 htT
    by_contra hne
    have hgap : 0 < |u t () - 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
    rcases htrace.eventually_small hgap with ⟨δ, hδ, hsmall⟩
    set s := min (δ / 2) (Tmax / 2) with hs_def
    have hs_pos : 0 < s := lt_min (by linarith) (by linarith)
    have hs_lt_δ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs_lt_T : s < Tmax := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hsup := hsmall s hs_pos hs_lt_δ
    simp only [unitPointDomain, u₀] at hsup
    -- hsup : |u s () - 1| < |u t () - 1|
    -- But u s () = u t () (constant on (0, Tmax))
    have heq := hconst s t ⟨hs_pos, hs_lt_T⟩ ⟨ht0, htT⟩
    rw [heq] at hsup
    exact lt_irrefl _ hsup
  -- FiniteHorizonAlternative fails for u ≡ 1
  rcases halt with hunb | hvan
  · -- First disjunct: u unbounded
    rcases hunb 1 with ⟨t, x, ht0, htT, _, hM⟩
    have hx : x = () := rfl
    rw [hx] at hM
    linarith [hone t ht0 htT]
  · -- Second disjunct: u vanishes
    rcases hvan (1 / 2) (by norm_num) with ⟨t, x, ht0, htT, _, hδ⟩
    have hx : x = () := rfl
    rw [hx] at hδ
    linarith [hone t ht0 htT]

end

end ShenWork.Paper2
