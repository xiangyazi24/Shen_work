/-
  Lemma 3.1, the `a = b = 0` branch (χ₀ ≤ 0).

  ## CORRECTION (supersedes the earlier "too-strong / false" finding)

  An earlier note in this file claimed the `a = b = 0` branch was FALSE
  for `χ₀ < 0` (chemotaxis survives → sup-norm can grow).  **That was
  WRONG** — it ignored the elliptic coupling to `v`.  The paper
  (arXiv 2512.14858, Lemma 3.1 (2)) proves the branch for the full
  `χ₀ ≤ 0`, and `a = b = 0` is a GENUINE case of Theorem 1.1 (2), not a
  formalization artifact.

  ## Why it is true for `χ₀ ≤ 0` (paper's argument)

  At a spatial maximum `x*` of `u(t,·)` (`∂ₓu(x*) = 0`, `Δu(x*) ≤ 0`):
    `chemotaxisDiv(x*) = u·v_xx·φ(v) + u·v_x²·φ'(v)`   (the `∂ₓu` term drops),
  with `φ(v) = (1+v)^{-β}`, `φ' = −β(1+v)^{-β-1} ≤ 0`.  The signal `v`
  solves the elliptic equation `v_xx = μv − νu^γ` (Neumann), and its OWN
  maximum principle gives the paper's key bound (3.2):
    `μ·v̄ ≤ ν·ū^γ`     (i.e. `μ·sup v ≤ ν·(sup u)^γ`),
  because `v = (μI − Δ)^{-1}(νu^γ) ≤ (μI − Δ)^{-1}(ν ū^γ) = ν ū^γ / μ`.
  At `x*` (`u(x*) = ū`): `μ v(x*) ≤ μ v̄ ≤ ν ū^γ = ν u(x*)^γ`, so
    `v_xx(x*) = μ v(x*) − ν u(x*)^γ ≤ 0`.
  Hence `u·v_xx·φ ≤ 0` and `u·v_x²·φ' ≤ 0`, so `chemotaxisDiv(x*) ≤ 0`,
  and with `χ₀ ≤ 0` (`−χ₀ ≥ 0`):
    `∂ₜu(x*) = Δu(x*) − χ₀·chemotaxisDiv(x*) ≤ 0`     (a = b = 0).
  So the spatial maximum (= sup-norm, `u ≥ 0`) is non-increasing.

  ## This file

  Provides the two reusable engines of that argument:
    * `v_elliptic_max_principle` — the paper's (3.2), proved via
      `MinPersistenceAtoms.elliptic_sup_bound`;
    * `supNorm_nonincreasing_of_dini` — the max-side Grönwall reduction
      (`SupNormNonincreasingOn` from a one-sided Dini condition).

  The remaining gap to CLOSE the branch is the Hamilton-max DINI step:
  formalize "at the argmax, `∂ₜu ≤ 0` ⇒ the sup-norm has right-Dini
  derivative ≤ 0" (paper Steps 1–3; the max-side mirror of the
  MinPersistence Hamilton machinery).  Then `supNorm_nonincreasing_of_dini`
  finishes.  No narrowing of the branch is needed.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.Statements
import ShenWork.Paper2.IntervalDomainMinPersistenceAtoms
import Mathlib.Analysis.ODE.Gronwall

open Filter Topology
open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint intervalDomainSupNorm)

noncomputable section

namespace ShenWork.Paper2.Lemma31Heat

/-- **Paper (3.2): elliptic maximum principle for the signal.**  If the
(lifted) signal `wv` solves `wv'' = μ·wv − ν·wu^γ` on `(0,1)` with Neumann
limits and `0 ≤ wu ≤ Mu`, then `μ·wv ≤ ν·Mu^γ` on `[0,1]`.  This is the
sign-control that makes the chemotaxis term non-positive at the `u`-max.

Proved by `MinPersistenceAtoms.elliptic_sup_bound` with source
`ν·wu^γ` (bounded by `ν·Mu^γ`). -/
theorem v_elliptic_max_principle
    {wv wu : ℝ → ℝ} {μ ν γ Mu : ℝ} (hμ : 0 < μ) (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hcont : ContinuousOn wv (Set.Icc (0:ℝ) 1))
    (hd1 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ wv y)
    (hd2 : ∀ y ∈ Set.Ioo (0:ℝ) 1, DifferentiableAt ℝ (deriv wv) y)
    (hPDE : ∀ y ∈ Set.Ioo (0:ℝ) 1,
      deriv (deriv wv) y = μ * wv y - ν * (wu y) ^ γ)
    (hwu_nonneg : ∀ y ∈ Set.Ioo (0:ℝ) 1, 0 ≤ wu y)
    (hwu_bdd : ∀ y ∈ Set.Ioo (0:ℝ) 1, wu y ≤ Mu)
    (hNeu0 : Filter.Tendsto (deriv wv) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hNeu1 : Filter.Tendsto (deriv wv) (nhdsWithin 1 (Set.Iio 1)) (nhds 0)) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, μ * wv x ≤ ν * Mu ^ γ := by
  -- Source `Src y := ν·wu y^γ`, bounded by `B := ν·Mu^γ`.
  set Src : ℝ → ℝ := fun y => ν * (wu y) ^ γ with hSrc_def
  set B : ℝ := ν * Mu ^ γ with hB_def
  have hSrc_bd : ∀ y ∈ Set.Ioo (0:ℝ) 1, |Src y| ≤ B := by
    intro y hy
    have h0 : 0 ≤ (wu y) ^ γ := Real.rpow_nonneg (hwu_nonneg y hy) γ
    have hmono : (wu y) ^ γ ≤ Mu ^ γ :=
      Real.rpow_le_rpow (hwu_nonneg y hy) (hwu_bdd y hy) hγ
    rw [hSrc_def, abs_of_nonneg (mul_nonneg hν h0)]
    exact mul_le_mul_of_nonneg_left hmono hν
  have hbound := ShenWork.MinPersistenceAtoms.elliptic_sup_bound
    hμ hcont hd1 hd2 (by
      intro y hy; rw [hPDE y hy]) hSrc_bd hNeu0 hNeu1
  intro x hx
  have hwx := hbound x hx
  -- `wv x ≤ B/μ` ⇒ `μ·wv x ≤ B = ν·Mu^γ`.
  rw [le_div_iff₀ hμ] at hwx
  rw [hB_def]
  linarith [hwx]

/-- **Max-side Grönwall reduction (reusable).**  If the sup-norm
trajectory `M(t) := ‖u(t)‖_∞` is continuous on `Ioo 0 T` and does not
increase to the right (one-sided Dini condition), then `M` is
non-increasing on `Ioo 0 T`.  The parabolic-maximum-principle conclusion
stripped of PDE content; the PDE enters only through the Dini hypothesis
(at the argmax, `∂ₜu ≤ 0`, established above for `χ₀ ≤ 0`, `a = b = 0`). -/
theorem supNorm_nonincreasing_of_dini
    {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hcont : ContinuousOn (fun t => intervalDomainSupNorm (u t))
      (Set.Ioo (0 : ℝ) T))
    (hDini : ∀ x ∈ Set.Ioo (0 : ℝ) T, ∀ r : ℝ, 0 < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x),
        (z - x)⁻¹ * (intervalDomainSupNorm (u z)
          - intervalDomainSupNorm (u x)) < r) :
    SupNormNonincreasingOn intervalDomain u (Set.Ioo (0 : ℝ) T) := by
  intro t₁ ht₁ t₂ ht₂ hle
  set M : ℝ → ℝ := fun t => intervalDomainSupNorm (u t) with hM_def
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht₁.1 hs.1, lt_of_le_of_lt hs.2 ht₂.2⟩
  have hcont' : ContinuousOn M (Set.Icc t₁ t₂) := hcont.mono hsub
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f := M) (f' := fun _ => 0) (δ := M t₁) (K := 0) (ε := 0)
    (a := t₁) (b := t₂)
    hcont'
    (by
      intro x hx r hr
      have hxmem : x ∈ Set.Ioo (0 : ℝ) T :=
        hsub (Set.Ico_subset_Icc_self hx)
      exact hDini x hxmem r hr)
    (le_refl _)
    (by intro x _; simp)
  have hbx := hgron t₂ (Set.right_mem_Icc.mpr hle)
  rwa [gronwallBound_ε0, mul_zero, Real.exp_zero, mul_one] at hbx

end ShenWork.Paper2.Lemma31Heat
