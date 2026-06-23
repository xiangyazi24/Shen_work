/-
  ShenWork/Paper2/IntervalChiNegPersistDischarge.lean

  **χ₀<0 FINAL — discharge of `Hpersist` via the INFLATED supersolution
  `Estar = ρ₀ • E_base` (ρ₀ > 1).**

  `baseEnvelope_of_residualSupply` (IntervalChiNegBoxExtendDischarge, landed)
  reduces the χ₀<0 base `TrajectoryHSigmaEnvelope` to the single carried per-mode
  endpoint margin

    Hpersist χ₀ δ Estar u flLeg r :
      ∀ ρ, 0 ≤ ρ → ρ ≤ δ → ∀ k,
        |e^{−ρλ_k}·cosineCoeffs (u r) k| + |flLeg ρ k| ≤ (1 − |χ₀|δ)·Estar k.

  This file DERIVES `Hpersist` for `Estar := ρ₀ • E_base` from:

  * (DERIVED) the σ = 0 specialisation of the LANDED per-mode divergence-Duhamel
    smoothing bound `hSigma_mode_duhamel_bound`, giving the logistic per-mode leg
    `|flLeg ρ k| = |duhamelEnergyCoeff 1 G ρ k| ≤ 2·C₀·M_k·√ρ` whenever the
    (r-shifted) logistic source `G` has the per-mode sup `|G k τ| ≤ M_k` on [0,ρ];
  * (DERIVED) the heat-leg contraction `|e^{−ρλ_k}·x_k| ≤ |x_k|` (`exp ≤ 1`);
  * (DERIVED) the ρ₀-inflation margin algebra closing
    `E_base k + 2C₀·Llog·√δ·E_base k ≤ (1 − |χ₀|δ)·ρ₀·E_base k`
    for `ρ₀ := (1 + 2C₀·Llog·√δ)/(1 − |χ₀|δ)`.

  * (CARRIED — exactly the standard local-existence / order-box input, named
    `hlocalexist`) the two `u`-specific facts that the divergence-form mild
    SOLUTION at the restart satisfies — and that ChemMildLocal supplies only as the
    SCALAR `ContractingWith` core, NOT as the envelope-lattice instantiation:
      (box)  |cosineCoeffs (u r) k| ≤ E_base k,        and
      (src)  |G k τ| ≤ Llog · E_base k  (the logistic source per-mode envelope).
    This is the order-box bound of the local mild solution on the restart interval
    — strictly WEAKER than, and distinct from, the χ₀<0 all-τ boundedness
    conclusion (it bounds only `u r` at the restart endpoint and its source
    envelope, never the global domination).

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegBoxExtendDischarge
import ShenWork.Paper2.IntervalBFormHSigmaDuhamelEnergy

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegPersistDischarge

open Real
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg one_add_lam_pos)
open ShenWork.Paper2.BFormHSigmaDuhamelMode (duhamelModeCoeff hSigma_mode_duhamel_bound)
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy (duhamelEnergyCoeff)
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier (linfty_multiplier_bound)
open ShenWork.Paper2.IntervalChiNegBoxExtendDischarge (Hpersist)

/-! ## The σ = 0 logistic per-mode L∞ bound (DERIVED from the landed mode bound). -/

/-- The Duhamel multiplier constant at `σ = 0`, `d = 1` (LANDED, via
`linfty_multiplier_bound`). -/
def C0 : ℝ := Classical.choose (linfty_multiplier_bound (le_refl (0:ℝ)) one_pos (1:ℝ) one_pos)

theorem C0_pos : 0 < C0 :=
  (Classical.choose_spec (linfty_multiplier_bound (le_refl (0:ℝ)) one_pos (1:ℝ) one_pos)).1

/-- **σ = 0 per-mode Duhamel L∞ bound.**  For `0 < s ≤ 1` and a continuous source
`F` with `|F k τ| ≤ M` on `[0,s]` (`0 ≤ M`), the mode-`k` Duhamel coefficient
satisfies `|duhamelEnergyCoeff 1 F s k| ≤ C0 · M · (2·√s)`.  This is the `σ = 0`,
weight-`1` specialisation of the LANDED `hSigma_mode_duhamel_bound`. -/
theorem duhamelEnergy_mode_abs_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {F : ℕ → ℝ → ℝ} (hFcont : ∀ k, Continuous (F k))
    (k : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hFbd : ∀ τ ∈ Set.Icc (0:ℝ) s, |F k τ| ≤ M) :
    |duhamelEnergyCoeff 1 F s k| ≤ C0 * M * (2 * Real.sqrt s) := by
  have hbd := hSigma_mode_duhamel_bound (le_refl (0:ℝ)) one_pos one_pos hs hs1
    (lam_nonneg k) (hFcont k) hM0 hFbd
  -- weight (1+λ_k)^(0/2) = 1
  have hw : (1 + lam k) ^ ((0:ℝ)/2) = 1 := by
    norm_num
  rw [hw, one_mul] at hbd
  -- duhamelEnergyCoeff 1 F s k = duhamelModeCoeff 1 (lam k) (F k) s
  have hcoeff : duhamelEnergyCoeff 1 F s k = duhamelModeCoeff 1 (lam k) (F k) s := rfl
  rw [hcoeff]
  -- s^((1-0)/2)/((1-0)/2) = √s / (1/2) = 2√s
  have hexp : s ^ (((1:ℝ) - 0)/2) / (((1:ℝ) - 0)/2) = 2 * Real.sqrt s := by
    have : ((1:ℝ) - 0)/2 = (1:ℝ)/2 := by norm_num
    rw [this]
    rw [Real.rpow_div_two_eq_sqrt _ hs.le, Real.rpow_one]
    field_simp
  rw [show C0 = Classical.choose (linfty_multiplier_bound (le_refl (0:ℝ)) one_pos (1:ℝ) one_pos)
    from rfl]
  calc |duhamelModeCoeff 1 (lam k) (F k) s|
      ≤ Classical.choose (linfty_multiplier_bound (le_refl (0:ℝ)) one_pos (1:ℝ) one_pos)
          * M * (s ^ (((1:ℝ) - 0)/2) / (((1:ℝ) - 0)/2)) := hbd
    _ = Classical.choose (linfty_multiplier_bound (le_refl (0:ℝ)) one_pos (1:ℝ) one_pos)
          * M * (2 * Real.sqrt s) := by rw [hexp]

/-! ## The carried standard local-existence / order-box input. -/

/-- **`LocalExist`** — the standard local-existence / order-box input for the
divergence-form mild SOLUTION `u` at the restart point `r` with logistic source
`G`: the order box `|cosineCoeffs (u r) k| ≤ E_base k` and the logistic source
per-mode envelope `|G k τ| ≤ Llog·E_base k`.  ChemMildLocal provides only the
SCALAR `ContractingWith` core for these; the envelope-lattice instantiation that
makes them hold for the actual `u` is the genuine local-existence content.  This is
strictly WEAKER than the χ₀<0 all-`τ` boundedness conclusion. -/
def LocalExist (E_base : ℕ → ℝ) (Llog : ℝ) (u : ℝ → ℝ → ℝ) (G : ℕ → ℝ → ℝ)
    (r : ℝ) : Prop :=
  (∀ k, |cosineCoeffs (u r) k| ≤ E_base k) ∧
  (∀ k, ∀ τ, |G k τ| ≤ Llog * E_base k)

/-! ## The ρ₀ inflation + margin algebra (DERIVED), discharging `Hpersist`. -/

/-- **`Hpersist_derived`** — the inflated-supersolution discharge of `Hpersist`.

Take `Estar := fun k => ρ₀ * E_base k` with the inflation factor
`ρ₀ := (1 + C0·Llog·(2·√δ))/(1 − |χ₀|δ)` (> 1 since the numerator > denominator
when the logistic term is positive), the logistic leg
`flLeg := fun ρ k => duhamelEnergyCoeff 1 G ρ k`, and the CARRIED order-box / source
envelope `hlocalexist : LocalExist E_base Llog u G r`.  Then `Hpersist` holds.

Heat leg: `|e^{−ρλ_k}·x_k| ≤ |x_k| ≤ E_base k` (exp ≤ 1 + box).
Logistic leg: `|flLeg ρ k| ≤ C0·(Llog·E_base k)·(2√ρ) ≤ C0·Llog·(2√δ)·E_base k`.
Sum ≤ (1 + C0·Llog·2√δ)·E_base k = (1 − |χ₀|δ)·ρ₀·E_base k. -/
theorem Hpersist_derived
    {E_base : ℕ → ℝ} (hE0 : ∀ k, 0 ≤ E_base k)
    {Llog χ₀ δ : ℝ} (hLlog : 0 ≤ Llog) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcontr : 0 < 1 - |χ₀| * δ)
    {u : ℝ → ℝ → ℝ} {G : ℕ → ℝ → ℝ} {r : ℝ}
    (hGcont : ∀ k, Continuous (G k))
    (hlocalexist : LocalExist E_base Llog u G r) :
    Hpersist χ₀ δ (fun k => ((1 + C0 * Llog * (2 * Real.sqrt δ)) / (1 - |χ₀| * δ))
        * E_base k) u (fun ρ k => duhamelEnergyCoeff 1 G ρ k) r := by
  obtain ⟨hbox, hsrc⟩ := hlocalexist
  set ρ₀ := (1 + C0 * Llog * (2 * Real.sqrt δ)) / (1 - |χ₀| * δ) with hρ₀
  intro ρ hρ0 hρδ k
  have hEk := hE0 k
  have hsqδ : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hC0 := C0_pos
  -- heat leg: |e^{−ρλ}·x| ≤ |x| ≤ E_base k
  have hexp_le : Real.exp (-(ρ * lam k)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := lam_nonneg k; nlinarith [hρ0, this]
  have hexp_nn : 0 ≤ Real.exp (-(ρ * lam k)) := (Real.exp_pos _).le
  have hheat : |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k| ≤ E_base k := by
    rw [abs_mul, abs_of_nonneg hexp_nn]
    calc Real.exp (-(ρ * lam k)) * |cosineCoeffs (u r) k|
        ≤ 1 * |cosineCoeffs (u r) k| :=
          mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)
      _ = |cosineCoeffs (u r) k| := one_mul _
      _ ≤ E_base k := hbox k
  -- logistic leg, two sub-cases on ρ = 0 vs ρ > 0
  have hMnn : 0 ≤ Llog * E_base k := mul_nonneg hLlog hEk
  have hlog : |duhamelEnergyCoeff 1 G ρ k| ≤ C0 * Llog * (2 * Real.sqrt δ) * E_base k := by
    rcases eq_or_lt_of_le hρ0 with hρeq | hρpos
    · -- ρ = 0 : duhamelEnergyCoeff over [0,0] = 0
      have hz : duhamelEnergyCoeff 1 G ρ k = 0 := by
        unfold duhamelEnergyCoeff duhamelModeCoeff
        rw [← hρeq]; simp
      rw [hz, abs_zero]
      have : 0 ≤ C0 * Llog * (2 * Real.sqrt δ) * E_base k := by positivity
      linarith
    · have hρ1 : ρ ≤ 1 := le_trans hρδ hδ1
      have hbd := duhamelEnergy_mode_abs_le hρpos hρ1 hGcont k hMnn
        (fun t _ => hsrc k t)
      -- |·| ≤ C0·(Llog·E_base k)·(2√ρ) ≤ C0·Llog·(2√δ)·E_base k
      have hsqle : Real.sqrt ρ ≤ Real.sqrt δ := Real.sqrt_le_sqrt hρδ
      have hstep : C0 * (Llog * E_base k) * (2 * Real.sqrt ρ)
          ≤ C0 * Llog * (2 * Real.sqrt δ) * E_base k := by
        have hpre : (0:ℝ) ≤ C0 * Llog * E_base k * 2 := by positivity
        have hle : C0 * Llog * E_base k * 2 * Real.sqrt ρ
            ≤ C0 * Llog * E_base k * 2 * Real.sqrt δ :=
          mul_le_mul_of_nonneg_left hsqle hpre
        calc C0 * (Llog * E_base k) * (2 * Real.sqrt ρ)
            = C0 * Llog * E_base k * 2 * Real.sqrt ρ := by ring
          _ ≤ C0 * Llog * E_base k * 2 * Real.sqrt δ := hle
          _ = C0 * Llog * (2 * Real.sqrt δ) * E_base k := by ring
      exact le_trans hbd hstep
  -- assemble the margin
  have hcne : (1 - |χ₀| * δ) ≠ 0 := ne_of_gt hcontr
  have hsum : E_base k + C0 * Llog * (2 * Real.sqrt δ) * E_base k
      = (1 - |χ₀| * δ) * (ρ₀ * E_base k) := by
    have hcancel : (1 - |χ₀| * δ) * ρ₀ = 1 + C0 * Llog * (2 * Real.sqrt δ) := by
      rw [hρ₀]; field_simp
    calc E_base k + C0 * Llog * (2 * Real.sqrt δ) * E_base k
        = (1 + C0 * Llog * (2 * Real.sqrt δ)) * E_base k := by ring
      _ = ((1 - |χ₀| * δ) * ρ₀) * E_base k := by rw [hcancel]
      _ = (1 - |χ₀| * δ) * (ρ₀ * E_base k) := by ring
  calc |Real.exp (-(ρ * lam k)) * cosineCoeffs (u r) k|
        + |duhamelEnergyCoeff 1 G ρ k|
      ≤ E_base k + C0 * Llog * (2 * Real.sqrt δ) * E_base k :=
        add_le_add hheat hlog
    _ = (1 - |χ₀| * δ) * (ρ₀ * E_base k) := hsum

/-! ## AxiomAudit -/

section AxiomAudit
#print axioms duhamelEnergy_mode_abs_le
#print axioms Hpersist_derived
end AxiomAudit

end ShenWork.Paper2.IntervalChiNegPersistDischarge
