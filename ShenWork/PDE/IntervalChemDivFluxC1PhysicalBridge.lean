/-
  ShenWork/PDE/IntervalChemDivFluxC1PhysicalBridge.lean

  G1 — the resolver pointwise C¹ flux-divergence Lipschitz, closed via the
  PHYSICAL bounded-weight route (NOT the cubic spectral `∑ k³` over-ask).

  The chemotaxis divergence `intervalDomainChemotaxisDiv p u (R u) y =
  ∂ₓ(lift u · ∂ₓ(R u) · (1+R u)^{-β})` expands (product/quotient/rpow rule) into

     ∂ₓu · g · q  +  u · ∂ₓ²v · q  −  β · u · g² · q′      (g = ∂ₓv, v = R u)

  where every RESOLVER factor is controlled by the PHYSICAL bounded-weight route:
    • `g = resolverGradReal`        — weight `kπ/(μ+λ_k) ≤ 1/(2√μ)`, ℓ²-summable
      (`intervalNeumannResolverR_grad_sup_lipschitz`), so `∂ₓv` is bounded and
      Lipschitz-in-`u` by the SOURCE ℓ¹/ℓ², not by `∑ k³`.
    • `∂ₓ²v = intervalNeumannResolverRLap`  — NOT `∑ k³`, but the ELLIPTIC
      IDENTITY `∂ₓ²v = μ·v − source` (`intervalNeumannResolverRLap_elliptic_identity`),
      so it is controlled by the resolver VALUE and the source value — again
      bounded-weight, the same trick that bypassed the eigen-cube regress.

  The DIFFERENCE of the two divergences is `K_u·D + K_g·D_g`, where
  `D = sup|Δ(lift u)|` and `D_g = sup|Δ(∂ₓ lift u)|`
  (`intervalDomainChemotaxisDiv_classical_K_D_form_interior`, proved entirely
  on the physical route).  The single residual analytic input — NOT supplied by
  the resolver, NOT by the bounded weight — is the parabolic-Schauder control of
  the trajectory's OWN spatial gradient `∂ₓu`: a Lipschitz `D_g ≤ L_u · D` in
  `u`.  This file makes that reduction EXPLICIT and machine-checked: given the
  parabolic input it collapses the two-dimensional `K_u·D + K_g·D_g` bound to the
  single-constant `K·D` shape the `hflux_lip` slot of
  `IntervalCoupledResolverBallEstimates` demands, with `K = K_u + K_g·L_u`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalCoupledClassicalBallEstimates

open ShenWork.Paper2 ShenWork.IntervalDomain ShenWork.PDE
open ShenWork.IntervalResolverLaplacianBridge
open ShenWork.IntervalCoupledClassicalBallEstimates

noncomputable section

namespace ShenWork.IntervalChemDivFluxC1PhysicalBridge

/-- **G1 (physical bounded-weight route) — single-constant `K·D` collapse.**

The chemotaxis flux-divergence Lipschitz `|chemDiv₁ − chemDiv₂| ≤ K·D` at every
interior point, derived from the proven two-dimensional physical bound
`≤ K_u·D + K_g·D_g` (whose resolver legs `L_R`, `L_H`, the `H` sup bound on
`RLap`, and `L_V` are ALL the bounded-weight quantities, never `∑ k³`) and the
ONE genuinely external input `hDg_le : D_g ≤ L_u · D` — the parabolic-Schauder
Lipschitz of the trajectory's own spatial gradient `∂ₓu` in `u`.  The resolver
contributes nothing to this last leg: `u` enters the flux as a raw factor whose
spatial derivative the sup ball does not see.

`K := K_u + K_g · L_u` is explicit and nonnegative. -/
theorem chemDivFlux_physical_KD_collapse
    {p : CM2Params} {T M G_u : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂)
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u)
    {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    {H : ℝ} (hHnn : 0 ≤ H)
    (hH₁ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H)
    (hH₂ : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0:ℝ) 1 →
      |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H)
    {D D_g L_V L_R L_H L_u : ℝ}
    (hDnn : 0 ≤ D) (hDgnn : 0 ≤ D_g)
    (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R) (hLHnn : 0 ≤ L_H) (hLunn : 0 ≤ L_u)
    (hu_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D)
    (hdu_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ τ)) x
        - deriv (intervalDomainLift (u₂ τ)) x| ≤ D_g)
    (hv_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x| ≤ L_V * D)
    (hg_diff : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (u₁ τ) x - resolverGradReal p (u₂ τ) x| ≤ L_R * D)
    (hH_diff : ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
      |intervalNeumannResolverRLap p (u₁ τ) y
        - intervalNeumannResolverRLap p (u₂ τ) y| ≤ L_H * D)
    -- the SINGLE residual external input (parabolic `C^{2,α}` regularity of `u`):
    (hDg_le : D_g ≤ L_u * D) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : intervalDomainPoint, y.1 ∈ Set.Ioo (0 : ℝ) 1 →
        |intervalDomainChemotaxisDiv p (u₁ τ) (v₁ τ) y
          - intervalDomainChemotaxisDiv p (u₂ τ) (v₂ τ) y| ≤ K * D := by
  classical
  obtain ⟨G, K_u, K_g, _hGnn, hKunn, hKgnn, hbound⟩ :=
    intervalDomainChemotaxisDiv_classical_K_D_form_interior
      hsnap₁ hsnap₂ hMnn hGunn hτ hHnn hH₁ hH₂
      hDnn hDgnn hLVnn hLRnn hLHnn
      hu_diff hdu_diff hv_diff hg_diff hH_diff
  refine ⟨K_u + K_g * L_u, by positivity, ?_⟩
  intro y hy
  refine (hbound y hy).trans ?_
  have hKgDg : K_g * D_g ≤ K_g * (L_u * D) := mul_le_mul_of_nonneg_left hDg_le hKgnn
  calc K_u * D + K_g * D_g
      ≤ K_u * D + K_g * (L_u * D) := by linarith
    _ = (K_u + K_g * L_u) * D := by ring

end ShenWork.IntervalChemDivFluxC1PhysicalBridge
