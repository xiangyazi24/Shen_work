/-
  Statement layer for Chen-Ruau-Shen,
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type
  source, I: Boundedness and global existence".

  This file introduces a bounded-domain PDE interface and states the paper's
  main results against that interface.  It deliberately does not reuse the toy
  predicates in `Paper2/Defs.lean`.
-/
import ShenWork.Paper2.Defs
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

/--
Abstract data for the smooth bounded Neumann domain used in Paper2.

The differential operators are intentionally bundled here: the statement layer
can express the paper PDE now, while later analytic work can instantiate these
fields for a concrete smooth bounded domain in `ℝ^N`.
-/
structure BoundedDomainData where
  Point : Type
  inside : Set Point
  boundary : Set Point
  volume : ℝ
  supNorm : (Point → ℝ) → ℝ
  infValue : (Point → ℝ) → ℝ
  integral : (Point → ℝ) → ℝ
  gradNorm : (Point → ℝ) → Point → ℝ
  timeDeriv : (ℝ → Point → ℝ) → ℝ → Point → ℝ
  laplacian : (Point → ℝ) → Point → ℝ
  chemotaxisDiv : CM2Params → (Point → ℝ) → (Point → ℝ) → Point → ℝ
  crossDiffusionEnergyTerm : CM2Params → ℝ → (Point → ℝ) → (Point → ℝ) → ℝ
  normalDeriv : (Point → ℝ) → Point → ℝ
  initialAdmissible : (Point → ℝ) → Prop
  classicalRegularity : ℝ → (ℝ → Point → ℝ) → (ℝ → Point → ℝ) → Prop

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
  fractional_decay :
    ∀ p : CM2Params, ∀ sigma q delta, 0 ≤ sigma → 1 ≤ q →
      0 < delta → delta < p.μ →
        ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
          fractionalNorm sigma q (semigroup t u) ≤
            C * t ^ (-sigma) * Real.exp (-delta * t) * lpNorm q u
  semigroup_continuity :
    ∀ sigma, 0 < sigma → sigma ≤ 1 →
      ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
        lpNorm 2 (fun x => semigroup t u x - u x) ≤
          C * t ^ sigma * fractionalNorm sigma 2 u
  embedding_general :
    ∀ sigma q k r, 0 ≤ sigma → 1 ≤ q → q ≤ r →
      k - (D.volume / r) < 2 * sigma - D.volume / q →
        ∃ C > 0, ∀ u : D.Point → ℝ,
          embeddingNorm k r sigma u ≤ C * fractionalNorm sigma q u
  embedding_same_q :
    ∀ sigma q theta, 0 ≤ theta → theta < 2 * sigma - D.volume / q →
      ∃ C > 0, ∀ u : D.Point → ℝ,
        embeddingNorm theta q sigma u ≤ C * fractionalNorm sigma q u
  divergence_bound :
    ∀ p : CM2Params,
      ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ phi : D.Point → ℝ,
        lpNorm q (divergenceSemigroup t phi) ≤
          C * (1 + t ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(p.μ) * t) * vectorLpNorm q phi
  fractional_divergence_bound :
    ∀ p : CM2Params, ∀ sigma q, 0 < sigma → 1 < q →
      ∃ C > 0, ∀ t > 0, ∀ phi : D.Point → ℝ,
        fractionalNorm sigma q (divergenceSemigroup t phi) ≤
          C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(p.μ / 2) * t) * vectorLpNorm q phi

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

lemma Lemma_2_1.fractional_decay
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_1 D p S)
    {sigma q delta : ℝ}
    (hsigma : 0 ≤ sigma) (hq : 1 ≤ q)
    (hdelta_pos : 0 < delta) (hdelta_mu : delta < p.μ) :
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.fractionalNorm sigma q (S.semigroup t u) ≤
        C * t ^ (-sigma) * Real.exp (-delta * t) * S.lpNorm q u :=
  h.1 sigma q delta hsigma hq hdelta_pos hdelta_mu

lemma Lemma_2_1.semigroup_continuity
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_1 D p S)
    {sigma : ℝ} (hsigma_pos : 0 < sigma) (hsigma_one : sigma ≤ 1) :
    ∃ C > 0, ∀ t > 0, ∀ u : D.Point → ℝ,
      S.lpNorm 2 (fun x => S.semigroup t u x - u x) ≤
        C * t ^ sigma * S.fractionalNorm sigma 2 u :=
  h.2 sigma hsigma_pos hsigma_one

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

lemma Lemma_2_2.embedding_general
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_2_2 D S)
    {sigma q k r : ℝ}
    (hsigma : 0 ≤ sigma) (hq : 1 ≤ q) (hqr : q ≤ r)
    (hcond : k - (D.volume / r) < 2 * sigma - D.volume / q) :
    ∃ C > 0, ∀ u : D.Point → ℝ,
      S.embeddingNorm k r sigma u ≤ C * S.fractionalNorm sigma q u :=
  h.1 sigma q k r hsigma hq hqr hcond

lemma Lemma_2_2.embedding_same_q
    {D : BoundedDomainData} {S : SemigroupEstimateData D}
    (h : Lemma_2_2 D S)
    {sigma q theta : ℝ}
    (htheta_nonneg : 0 ≤ theta)
    (hcond : theta < 2 * sigma - D.volume / q) :
    ∃ C > 0, ∀ u : D.Point → ℝ,
      S.embeddingNorm theta q sigma u ≤ C * S.fractionalNorm sigma q u :=
  h.2 sigma q theta htheta_nonneg hcond

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

lemma Lemma_2_3.divergence_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_3 D p S) :
    ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.lpNorm q (S.divergenceSemigroup t phi) ≤
        C * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ) * t) * S.vectorLpNorm q phi :=
  h

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

lemma Lemma_2_4.fractional_divergence_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Lemma_2_4 D p S)
    {sigma q : ℝ} (hsigma : 0 < sigma) (hq : 1 < q) :
    ∃ C > 0, ∀ t > 0, ∀ phi : D.Point → ℝ,
      S.fractionalNorm sigma q (S.divergenceSemigroup t phi) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(p.μ / 2) * t) * S.vectorLpNorm q phi :=
  h sigma q hsigma hq

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
  fractional_decay := by
    intro p sigma q delta _hsigma _hq _hdelta_pos _hdelta_mu
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    norm_num
  semigroup_continuity := by
    intro sigma _hsigma_pos _hsigma_one
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht u
    norm_num
  embedding_general := by
    intro sigma q k r _hsigma _hq _hqr _hcond
    refine ⟨1, zero_lt_one, ?_⟩
    intro u
    norm_num
  embedding_same_q := by
    intro sigma q theta _htheta _hcond
    refine ⟨1, zero_lt_one, ?_⟩
    intro u
    norm_num
  divergence_bound := by
    intro p
    refine ⟨1, zero_lt_one, ?_⟩
    intro q hq t ht phi
    norm_num
  fractional_divergence_bound := by
    intro p sigma q _hsigma _hq
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht phi
    norm_num

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

def Lemma_2_5 : Prop :=
  ∀ beta v : ℝ, 0 < beta → 0 < v →
    beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta beta

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

theorem Lemma_2_5_proved : Lemma_2_5 := by
  intro beta v hbeta hv
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
  Lemma_2_5_proved beta v hbeta hv

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

/-- If `beta ≤ gamma`, the Lemma 2.5 pointwise expression at `beta` is also
bounded by the larger sharp constant `Psi_beta gamma`. -/
theorem Lemma_2_5_pointwise_bound_le_larger_Psi_beta
    {beta gamma v : ℝ} (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hbg : beta ≤ gamma) (hv : 0 < v) :
    beta * v / (1 + v) ^ (1 + beta) ≤ Psi_beta gamma := by
  exact le_trans
    (Lemma_2_5_pointwise_bound hbeta hv)
    (Psi_beta_monotoneOn_Ici hbeta.le hgamma hbg)

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

lemma Lemma_2_6.lp_bound
    {D : BoundedDomainData}
    (h : Lemma_2_6 D)
    {N : ℝ} (hN : 0 < N) {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hhyp : AbstractLpBootstrapHypothesis D u N T rho p0)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    LpPowerBoundedBefore D pExp T u :=
  h N hN u T rho p0 hhyp henergy pExp hpExp

lemma Lemma_2_6.lp_bound_of_data
    {D : BoundedDomainData}
    (h : Lemma_2_6 D)
    {N : ℝ} (hN : 0 < N) {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hrho : 0 < rho) (hT : 0 < T)
    (hp0 : max 1 (rho * N / 2) < p0)
    (hp0_bound : LpPowerBoundedBefore D p0 T u)
    (henergy : LpBootstrapEnergyInequality D u T rho p0)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    LpPowerBoundedBefore D pExp T u :=
  h.lp_bound hN ⟨hrho, hT, hp0, hp0_bound⟩ henergy hpExp

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

lemma Corollary_2_1.lp_bound
    {D : BoundedDomainData} {p : CM2Params}
    (h : Corollary_2_1 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hboot :
      ∃ rho > 0, CrossDiffusionBootstrapEstimate D p T rho u v ∧
        ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
          LpPowerBoundedBefore D p0 T u)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    LpPowerBoundedBefore D pExp T u :=
  h T hT u v hsol hboot pExp hpExp

lemma Corollary_2_1.lp_bound_of_bootstrap_data
    {D : BoundedDomainData} {p : CM2Params}
    (h : Corollary_2_1 D p)
    {T rho p0 : ℝ} (hT : 0 < T) (hrho : 0 < rho)
    {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hcross : CrossDiffusionBootstrapEstimate D p T rho u v)
    (hp0 : max 1 (rho * (p.N : ℝ) / 2) < p0)
    (hp0_bound : LpPowerBoundedBefore D p0 T u)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    LpPowerBoundedBefore D pExp T u :=
  h.lp_bound hT hsol
    ⟨rho, hrho, hcross, p0, hp0, hp0_bound⟩ hpExp

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

lemma Proposition_2_1.signal_lp_bound
    {D : BoundedDomainData} {p : CM2Params} {S : SemigroupEstimateData D}
    (h : Proposition_2_1 D p S)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp : ℝ} (hpExp : 1 ≤ pExp)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    S.lpNorm pExp (v t) ≤
      (p.ν / p.μ) * S.lpNorm pExp (fun x => (u t x) ^ p.γ) :=
  h T hT u v hsol pExp hpExp t ht0 htT

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
  fractional_decay := by
    intro p sigma q delta hsigma hq hdelta_pos hdelta_mu
    refine ⟨1, by norm_num, ?_⟩
    intro t ht u
    have hnorm_nonneg : 0 ≤ proposition21CounterLpNorm q u := by
      unfold proposition21CounterLpNorm
      split_ifs <;> norm_num
    have hmain :
        0 ≤ t ^ (-sigma) * Real.exp (-(delta * t)) *
          proposition21CounterLpNorm q u :=
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
        hnorm_nonneg
    simpa [one_mul, neg_mul] using hmain
  semigroup_continuity := by
    intro sigma hsigma_pos hsigma_one
    refine ⟨1, by norm_num, ?_⟩
    intro t ht u
    have hzero : (fun x : proposition21CounterDomain.Point => u x - u x) () ≠
        (1 / 2 : ℝ) := by norm_num
    simp [proposition21CounterLpNorm]
  embedding_general := by
    intro sigma q k r hsigma hq hqr hcond
    refine ⟨1, by norm_num, ?_⟩
    intro u
    simp
  embedding_same_q := by
    intro sigma q theta htheta hcond
    refine ⟨1, by norm_num, ?_⟩
    intro u
    simp
  divergence_bound := by
    intro p
    refine ⟨1, by norm_num, ?_⟩
    intro q hq t ht phi
    have hzero :
        (fun x : proposition21CounterDomain.Point =>
          (fun _ _ _ => (0 : ℝ)) t phi x) () ≠ (1 / 2 : ℝ) := by norm_num
    simp [proposition21CounterLpNorm]
  fractional_divergence_bound := by
    intro p sigma q hsigma hq
    refine ⟨1, by norm_num, ?_⟩
    intro t ht phi
    simp

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

lemma Proposition_2_2.weighted_gradient
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_2 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp : ℝ} (hpExp : 1 < pExp) :
    ∃ Mstar > 0, WeightedGradientEstimate D pExp p.β p.γ Mstar T u v :=
  h T hT u v hsol pExp hpExp

lemma Proposition_2_2.weighted_gradient_bound
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_2 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp t : ℝ} (hpExp : 1 < pExp) (ht0 : 0 < t) (htT : t < T) :
    ∃ Mstar > 0,
      D.integral (fun x => (D.gradNorm (v t) x) ^ (2 * pExp) / (v t x) ^ pExp) ≤
        Mstar * D.integral (fun x => (u t x) ^ (p.γ * pExp)) :=
  by
    rcases h.weighted_gradient hT hsol hpExp with
      ⟨Mstar, hMstar, hestimate⟩
    exact ⟨Mstar, hMstar, hestimate.first ht0 htT⟩

lemma Proposition_2_2.weighted_ratio_gradient_bound
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_2 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp t : ℝ} (hpExp : 1 < pExp) (ht0 : 0 < t) (htT : t < T) :
    ∃ Mstar > 0,
      D.integral
          (fun x =>
            (D.gradNorm (v t) x) ^ (2 * pExp) /
              (1 + v t x) ^ ((1 + p.β) * pExp)) ≤
        (Theta_beta p.β) ^ pExp * Mstar *
          D.integral (fun x => (u t x) ^ (p.γ * pExp)) :=
  by
    rcases h.weighted_gradient hT hsol hpExp with
      ⟨Mstar, hMstar, hestimate⟩
    exact ⟨Mstar, hMstar, hestimate.second ht0 htT⟩

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

lemma Proposition_2_3.weighted_signal
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_3 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp eps : ℝ} (hpExp : max 1 p.β < pExp) (heps : 0 < eps) :
    ∃ Ceps > 0, WeightedSignalEstimate D pExp p.β p.γ eps Ceps T u v :=
  h T hT u v hsol pExp hpExp eps heps

lemma Proposition_2_3.weighted_signal_bound
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_3 D p)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {pExp eps t : ℝ} (hpExp : max 1 p.β < pExp)
    (heps : 0 < eps) (ht0 : 0 < t) (htT : t < T) :
    ∃ Ceps > 0,
      D.integral (fun x => (v t x) ^ (pExp + 1) / (1 + v t x) ^ p.β) ≤
        eps *
            D.integral
              (fun x => (u t x) ^ (p.γ * (pExp + 1)) / (1 + v t x) ^ p.β) +
          Ceps *
            (D.integral
              (fun x => v t x / (1 + v t x) ^ (p.β / (pExp + 1)))) ^ (pExp + 1) :=
  by
    rcases h.weighted_signal hT hsol hpExp heps with
      ⟨Ceps, hCeps, hestimate⟩
    exact ⟨Ceps, hCeps, hestimate.bound ht0 htT⟩

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

lemma Proposition_2_4.mass_conserved
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_4 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (htrace : InitialTrace D u₀ u)
    (ha : p.a = 0) (hb : p.b = 0) :
    MassConservedBefore D T u₀ u :=
  (h u₀ hu₀ T hT u v hsol htrace).1 ha hb

lemma Proposition_2_4.logistic_mass_upper
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_4 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (htrace : InitialTrace D u₀ u)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    LogisticMassUpperBoundBefore D p T u₀ u :=
  (h u₀ hu₀ T hT u v hsol htrace).2 ha hb

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

lemma Proposition_2_5.bounded_before
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_2_5 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {Tmax : ℝ} (hTmax : 0 < Tmax) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p Tmax u v)
    (htrace : InitialTrace D u₀ u)
    {pExp : ℝ}
    (hpExp :
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp)
    (hLp : LpPowerBoundedBefore D pExp Tmax u) :
    IsPaper2BoundedBefore D Tmax u :=
  h u₀ hu₀ Tmax hTmax u v hsol htrace pExp hpExp hLp

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

lemma Lemma_2_7.lp_bound
    {D : BoundedDomainData}
    (h : Lemma_2_7 D)
    {u : ℝ → D.Point → ℝ} {T pExp C1 C2 C3 C4 eps alpha : ℝ}
    (hT : 0 < T) (hpExp : 1 < pExp)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 < C4)
    (heps : 0 < eps) (heps_alpha : eps ≤ alpha)
    (hdiff :
      ∀ t, 0 < t → t < T →
        deriv (fun τ => D.integral (fun x => (u τ x) ^ pExp)) t +
            C3 * D.integral (fun x => (u t x) ^ (pExp + alpha - eps)) ≤
          C1 + C2 * D.integral (fun x => (u t x) ^ pExp) -
            C4 * D.integral (fun x => (u t x) ^ (pExp + alpha))) :
    LpPowerBoundedBefore D pExp T u :=
  h u T pExp C1 C2 C3 C4 eps alpha
    hT hpExp hC1 hC2 hC3 hC4 heps heps_alpha hdiff

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

lemma Lemma_3_1.nonminimal_sup_norm_monotone
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_3_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    {t₀ : ℝ} (ht₀_pos : 0 < t₀) (ht₀_T : t₀ < T)
    (hsup : (p.a / p.b) ^ (1 / p.α) < D.supNorm (u t₀)) :
    SupNormNonincreasingOn D u (Set.Ioc (0 : ℝ) t₀) :=
  (h hχ).1 ha hb T hT u v hsol t₀ ht₀_pos ht₀_T hsup

lemma Lemma_3_1.minimal_sup_norm_monotone
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_3_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v) :
    SupNormNonincreasingOn D u (Set.Ioo (0 : ℝ) T) :=
  (h hχ).2 ha hb T hT u v hsol

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

def Lemma_4_1 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
  ∀ T > 0, ∀ u v : ℝ → D.Point → ℝ,
    IsPaper2ClassicalSolution D p T u v →
      InitialTrace D u₀ u →
        ∀ eps > 0, ∀ pExp > 1, ∃ Ceps > 0,
          LpMassGradientInterpolationEstimate D pExp eps Ceps T u

lemma Lemma_4_1.interpolation_estimate
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_4_1 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (htrace : InitialTrace D u₀ u)
    {eps pExp : ℝ} (heps : 0 < eps) (hpExp : 1 < pExp) :
    ∃ Ceps > 0, LpMassGradientInterpolationEstimate D pExp eps Ceps T u :=
  h u₀ hu₀ T hT u v hsol htrace eps heps pExp hpExp

lemma Lemma_4_1.interpolation_bound
    {D : BoundedDomainData} {p : CM2Params}
    (h : Lemma_4_1 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (htrace : InitialTrace D u₀ u)
    {eps pExp t : ℝ} (heps : 0 < eps) (hpExp : 1 < pExp)
    (ht0 : 0 < t) (htT : t < T) :
    ∃ Ceps > 0,
      D.integral (fun x => (u t x) ^ pExp) ≤
        eps *
            D.integral
              (fun x => (u t x) ^ (pExp - 2) * (D.gradNorm (u t) x) ^ 2) +
          Ceps * (D.integral (u t)) ^ pExp :=
  by
    rcases h.interpolation_estimate hu₀ hT hsol htrace heps hpExp with
      ⟨Ceps, hCeps, hestimate⟩
    exact ⟨Ceps, hCeps, hestimate.bound ht0 htT⟩

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

/-- Paper2 Remark 1.6 threshold `(1.30c)`, identical to `χ_β`. -/
def remark16ChiStarWeak (p : CM2Params) : ℝ :=
  2 * (2 * p.β - 1) / max 2 (p.γ * (p.N : ℝ))

lemma remark16ChiStarWeak_eq_chiBeta (p : CM2Params) :
    remark16ChiStarWeak p = chiBeta p := by
  rfl

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

lemma Proposition_1_1.solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Proposition_1_1 D p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      FiniteHorizonAlternative D Tmax u ∧
      (1 ≤ p.m → MGeOneFiniteHorizonAlternative D Tmax u) :=
  h u₀ hu₀

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

lemma Theorem_1_1.nonminimal_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      (∀ t, 0 < t → t < Tmax →
        D.supNorm (u t) ≤ max (D.supNorm u₀) ((p.a / p.b) ^ (1 / p.α))) ∧
      (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v) :=
  (h hχ).1 ha hb u₀ hu₀

lemma Theorem_1_1.nonminimal_bounded_before_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u ∧
      (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v) := by
  rcases h.nonminimal_solution hχ ha hb hu₀ with
    ⟨Tmax, hTmax, u, v, hsol, htrace, hbound, hglobal⟩
  refine ⟨Tmax, hTmax, u, v, hsol, htrace, ?_, hglobal⟩
  exact ⟨max (D.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)), hbound⟩

lemma Theorem_1_1.nonminimal_global_bounded_before_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u := by
  rcases h.nonminimal_bounded_before_solution hχ ha hb hu₀ with
    ⟨Tmax, hTmax, u, v, _hsol, htrace, hbound, hglobal⟩
  exact ⟨Tmax, hTmax, u, v, hglobal hm, htrace, hbound⟩

lemma Theorem_1_1.minimal_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      (∀ t, 0 < t → t < Tmax → D.supNorm (u t) ≤ D.supNorm u₀) ∧
      (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v) :=
  (h hχ).2 ha hb u₀ hu₀

lemma Theorem_1_1.minimal_bounded_before_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u ∧
      (1 ≤ p.m → IsPaper2GlobalClassicalSolution D p u v) := by
  rcases h.minimal_solution hχ ha hb hu₀ with
    ⟨Tmax, hTmax, u, v, hsol, htrace, hbound, hglobal⟩
  refine ⟨Tmax, hTmax, u, v, hsol, htrace, ?_, hglobal⟩
  exact ⟨D.supNorm u₀, hbound⟩

lemma Theorem_1_1.minimal_global_bounded_before_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_1 D p)
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u := by
  rcases h.minimal_bounded_before_solution hχ ha hb hu₀ with
    ⟨Tmax, hTmax, u, v, _hsol, htrace, hbound, hglobal⟩
  exact ⟨Tmax, hTmax, u, v, hglobal hm, htrace, hbound⟩

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

lemma Theorem_1_2.sublinear_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_2 D p)
    (ha : 0 ≤ p.a) (hb : 0 ≤ p.b) (hβ : 1 ≤ p.β)
    (hm_pos : 0 < p.m) (hm_lt : p.m < 1)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  (h ha hb hβ).1 hm_pos hm_lt u₀ hu₀

lemma Theorem_1_2.linear_solution
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_2 D p)
    (ha : 0 ≤ p.a) (hb : 0 ≤ p.b) (hβ : 1 ≤ p.β)
    (hm : p.m = 1) (hχ : p.χ₀ < chiBeta p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  (h ha hb hβ).2 hm hχ u₀ hu₀

lemma Theorem_1_2.linear_solution_of_min_half_sqrt
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_2 D p)
    (ha : 0 ≤ p.a) (hb : 0 ≤ p.b) (hβ : 1 ≤ p.β)
    (hm : p.m = 1)
    (hχ : p.χ₀ < min (chiBeta p / 2) (Real.sqrt (chiBeta p)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.linear_solution ha hb hβ hm
    (lt_chiBeta_of_lt_min_half_sqrt p hβ hχ) hu₀

lemma Theorem_1_2.linear_solution_of_remark16_weak
    {D : BoundedDomainData} {p : CM2Params}
    (h : Theorem_1_2 D p)
    (ha : 0 ≤ p.a) (hb : 0 ≤ p.b) (hβ : 1 ≤ p.β)
    (hm : p.m = 1) (hχ : p.χ₀ < remark16ChiStarWeak p)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.linear_solution ha hb hβ hm
    (by simpa [remark16ChiStarWeak_eq_chiBeta] using hχ) hu₀

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

lemma Theorem_1_3.finite_horizon_solution
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hcond : StrongLogisticCondition p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  (h ha hb hm_pos hcond).1 u₀ hu₀

lemma Theorem_1_3.global_solution
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hcond : StrongLogisticCondition p C) (hm : 1 ≤ p.m)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  (h ha hb hm_pos hcond).2 hm u₀ hu₀

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

lemma Theorem_1_3.finite_horizon_solution_of_alpha_gt_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hβ : 0 ≤ p.β) (hα : p.m + p.γ - 1 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_alpha_gt_m_add_gamma_sub_one hβ hα) hu₀

lemma Theorem_1_3.global_solution_of_alpha_gt_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hm : 1 ≤ p.m) (hβ : 0 ≤ p.β)
    (hα : p.m + p.γ - 1 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_alpha_gt_m_add_gamma_sub_one hβ hα) hm hu₀

lemma Theorem_1_3.finite_horizon_solution_of_alpha_gt_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : 2 * p.m + p.γ - 2 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_alpha_gt_two_mul_m_add_gamma_sub_two hβ hα) hu₀

lemma Theorem_1_3.global_solution_of_alpha_gt_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hm : 1 ≤ p.m) (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : 2 * p.m + p.γ - 2 < p.α)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_alpha_gt_two_mul_m_add_gamma_sub_two hβ hα)
    hm hu₀

lemma Theorem_1_3.finite_horizon_solution_of_critical_m_add_gamma_sub_one_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_m_add_gamma_sub_one_low_dimension
      hβ hα hdim)
    hu₀

lemma Theorem_1_3.global_solution_of_critical_m_add_gamma_sub_one_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hm : 1 ≤ p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_m_add_gamma_sub_one_low_dimension
      hβ hα hdim)
    hm hu₀

lemma Theorem_1_3.finite_horizon_solution_of_critical_two_mul_m_add_gamma_sub_two_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two_low_dimension
      hβ hα hdim)
    hu₀

lemma Theorem_1_3.global_solution_of_critical_two_mul_m_add_gamma_sub_two_low_dimension
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hm : 1 ≤ p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hdim : (p.N : ℝ) * p.α ≤ 2)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two_low_dimension
      hβ hα hdim)
    hm hu₀

lemma Theorem_1_3.finite_horizon_solution_of_critical_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_m_add_gamma_sub_one hβ hα hχ) hu₀

lemma Theorem_1_3.global_solution_of_critical_m_add_gamma_sub_one
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hm : 1 ≤ p.m)
    (hβ : 0 ≤ p.β) (hα : p.α = p.m + p.γ - 1)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_m_add_gamma_sub_one hβ hα hχ) hm hu₀

lemma Theorem_1_3.finite_horizon_solution_of_critical_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u :=
  h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two hβ hα hχ)
    hu₀

lemma Theorem_1_3.global_solution_of_critical_two_mul_m_add_gamma_sub_two
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b) (hm_pos : 0 < p.m)
    (hm : 1 ≤ p.m)
    (hβ : (1 / 2 : ℝ) ≤ p.β)
    (hα : p.α = 2 * p.m + p.γ - 2)
    (hχ :
      positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          Real.sqrt
            (8 * p.b /
              (positivePart ((p.N : ℝ) * p.α - 2) *
                Theta_beta (2 * p.β - 1) * C.K)))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u :=
  h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_critical_two_mul_m_add_gamma_sub_two hβ hα hχ)
    hm hu₀

lemma Theorem_1_3.finite_horizon_solution_of_remark16_chiStar1
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar1 p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u := by
  have hm_pos : 0 < p.m := by
    rw [hm]
    norm_num
  exact h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_remark16_chiStar1 hβ hm hα hdim hχ) hu₀

lemma Theorem_1_3.global_solution_of_remark16_chiStar1
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar1 p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u := by
  have hm_pos : 0 < p.m := by
    rw [hm]
    norm_num
  have hm_ge : 1 ≤ p.m := by
    rw [hm]
  exact h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_remark16_chiStar1 hβ hm hα hdim hχ) hm_ge hu₀

lemma Theorem_1_3.finite_horizon_solution_of_remark16_chiStar2
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar2 p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u := by
  have hm_pos : 0 < p.m := by
    rw [hm]
    norm_num
  exact h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_remark16_chiStar2 hβ hm hα hdim hχ) hu₀

lemma Theorem_1_3.global_solution_of_remark16_chiStar2
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < remark16ChiStar2 p C)
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u := by
  have hm_pos : 0 < p.m := by
    rw [hm]
    norm_num
  have hm_ge : 1 ≤ p.m := by
    rw [hm]
  exact h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_remark16_chiStar2 hβ hm hα hdim hχ) hm_ge hu₀

lemma Theorem_1_3.finite_horizon_solution_of_remark16_min_chiStar12
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < min (remark16ChiStar1 p C) (remark16ChiStar2 p C))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ Tmax > 0, ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2ClassicalSolution D p Tmax u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2BoundedBefore D Tmax u := by
  have hm_pos : 0 < p.m := by
    rw [hm]
    norm_num
  exact h.finite_horizon_solution ha hb hm_pos
    (StrongLogisticCondition.of_remark16_min_chiStar12 hβ hm hα hdim hχ) hu₀

lemma Theorem_1_3.global_solution_of_remark16_min_chiStar12
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (h : Theorem_1_3 D p C)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1) (hα : p.α = p.γ)
    (hdim : 2 < (p.N : ℝ) * p.γ)
    (hχ : p.χ₀ < min (remark16ChiStar1 p C) (remark16ChiStar2 p C))
    {u₀ : D.Point → ℝ} (hu₀ : PositiveInitialDatum D u₀) :
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      IsPaper2Bounded D u := by
  have hm_pos : 0 < p.m := by
    rw [hm]
    norm_num
  have hm_ge : 1 ≤ p.m := by
    rw [hm]
  exact h.global_solution ha hb hm_pos
    (StrongLogisticCondition.of_remark16_min_chiStar12 hβ hm hα hdim hχ)
    hm_ge hu₀

end

end ShenWork.Paper2
