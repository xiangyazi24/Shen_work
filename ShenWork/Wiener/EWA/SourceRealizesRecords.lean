import ShenWork.Wiener.EWA.SourceRealizesAssembly
import ShenWork.Wiener.EWA.ChemDivEval
import ShenWork.Wiener.EWA.GrowthEvalBridge

/-!
# EWA brick (χ₀<0 Route A′) — the realized-source `EWARealizesOn` RECORDS

`realizes_of_picardFixedPoint` (`SourceRealizesAssembly.lean`) carries four atoms per
Duhamel leg: the realized real-space function `w_chem` / `w_log`, the full-circle
realization record `H_chem` / `H_log : EWARealizesOn …`, and the lift-match
`hw_chem` / `hw_log`.  This file CONSTRUCTS those records.

## Architecture

* `w_chem s := fun x => intervalDomainChemotaxisDiv p (realSlice u_star s)
   (coupledChemicalConcentration p (realSlice u_star) s) x` so that
  `hw_chem s : intervalDomainLift (w_chem s) = coupledChemDivSourceLift … s` is `rfl`
  (read `coupledChemDivSourceLift`, `IntervalCoupledSourceTimeC1.lean:17`).
* `w_log s := intervalLogisticSource p (realSlice u_star s)`, likewise `rfl`-matched.

The `EWARealizesOn` fields:
* **even-real**: `chemDivEWA` is even-real (`chemDivEWA_evenReal`), `incl growthEWA`
  is even-real (`growthEWA_evenReal` + `.incl`) — from the carried `EvenRealEWA u_star`.
* **`eval_eq`** (full circle): `evalST_eq_cosineSynthesis_of_even_real` gives the cosine
  synthesis of `ewaCosCoeffAt`; the NON-CIRCULAR coefficient bridge
  `ewaCosCoeffAt_eq_cosineCoeffs_of_even_real` identifies `ewaCosCoeffAt … = cosineCoeffs
  (lift)` from the committed pointwise eval bridge on `Ioo 0 1`
  (`evalST_chemDivEWA_eq_coupledChemDivSourceLift` / `evalST_growthEWA_eq_logisticLifted`).
* **`is_cosine_series`**: the same synthesis read on the interval, transferred through the
  even-real circle identity (`eval_eq` holds at ALL `x`; the eval bridge gives the lift on
  the interior).
* **`summable_cos`**: INTRINSIC from the even-real slice (`ewaCosCoeffAt_abs_summable`),
  congr'd to `cosineCoeffs (lift)` by the coefficient identity.

## CARRIED analytic atoms (exactly what the committed bridges require)

ChemDiv (per `evalST_chemDivEWA_eq_coupledChemDivSourceLift`, on `Ioo 0 1`):
`hgrad` (resolver gradient ℓ¹ majorant), `h_flux_nbhd` (flux value agreement on the
open interval), `h_flux_diff` (real differentiability of `chemFluxLifted`).
Logistic (per `evalST_growthEWA_eq_logisticLifted`, on `Icc 0 1`):
`h_u` (the `u`-factor value realization), `h_uα` (the `u^α`-factor value realization).
Plus the fixed point's parity `hER_star : EvenRealEWA u_star` (discharged separately).

No `sorry`, `axiom`, `native_decide`, or `admit`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceLift coupledLogisticSourceLift coupledChemicalConcentration)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Grade-drop identity for `evalST`. -/

/-- The `incl (0 ≤ 0)` self-inclusion is invisible to `evalST` (slices agree
coefficientwise via `coeff_sliceWA_incl`). -/
theorem evalST_incl0_self (F : EWA T 0) (τ : TimeDom T) (x : WA.Circ) :
    evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 0) F) = evalST τ x F := by
  rw [evalST_apply, evalST_apply]
  congr 1
  apply WA.ext
  funext n
  exact coeff_sliceWA_incl (by omega) F τ n

/-! ### Continuity of a cosine series and the lift; the `Ioo → Icc` extension. -/

/-- A cosine series with absolutely summable coefficients is globally continuous
(`|cosineMode k x| ≤ 1`, so each term is bounded by `|c k|`). -/
theorem cosineSeries_continuous {c : ℕ → ℝ} (hc : Summable (fun k => |c k|)) :
    Continuous (fun x : ℝ => ∑' k : ℕ, c k * cosineMode k x) := by
  refine continuous_tsum (fun k => continuous_const.mul ?_) hc (fun k x => ?_)
  · unfold ShenWork.CosineSpectrum.cosineMode; fun_prop
  · rw [Real.norm_eq_abs, abs_mul]
    have hcos : |cosineMode k x| ≤ 1 := by
      unfold ShenWork.CosineSpectrum.cosineMode; exact Real.abs_cos_le_one _
    calc |c k| * |cosineMode k x| ≤ |c k| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |c k| := mul_one _

/-- The lift of a continuous interval-domain function is continuous on `[0,1]`
(`continuousOn_iff_continuous_restrict` + `intervalDomainLift = w` on `[0,1]`). -/
theorem lift_continuousOn_Icc {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.Icc (0 : ℝ) 1).restrict (intervalDomainLift w) = w := by
    funext ⟨y, hy⟩
    simp only [Set.restrict_apply, intervalDomainLift]
    rw [dif_pos hy]; exact congr_arg w (Subtype.ext rfl)
  rw [heq]; exact hw

/-- **`Ioo → Icc` agreement.**  Two functions that agree on `(0,1)`, one continuous on
`[0,1]` and the other globally continuous, agree on `[0,1] = closure (0,1)` — proved by
a sequential limit through the interior. -/
theorem eqOn_Icc_of_eqOn_Ioo {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hg : Continuous g)
    (hfg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x = g x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x := by
  intro x hx
  have hclos : x ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; exact hx
  rw [mem_closure_iff_seq_limit] at hclos
  obtain ⟨xseq, hxseq_mem, hxseq_lim⟩ := hclos
  have hcontAt : ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) x := hf x hx
  have hlimf : Filter.Tendsto (fun n => f (xseq n)) Filter.atTop (nhds (f x)) := by
    apply hcontAt.tendsto.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hxseq_lim, Filter.Eventually.of_forall
      (fun n => Set.Ioo_subset_Icc_self (hxseq_mem n))⟩
  have hlimg : Filter.Tendsto (fun n => g (xseq n)) Filter.atTop (nhds (g x)) :=
    (hg.tendsto x).comp hxseq_lim
  have heqseq : (fun n => f (xseq n)) = (fun n => g (xseq n)) :=
    funext (fun n => hfg (xseq n) (hxseq_mem n))
  rw [heqseq] at hlimf
  exact tendsto_nhds_unique hlimf hlimg

/-! ### The chemDiv realized-source record. -/

/-- The realized real-space chemDiv source slice (lift-matches `coupledChemDivSourceLift`
by `rfl`). -/
def wChem (p : CM2Params) (u_star : EWA T 1) :
    ℝ → intervalDomainPoint → ℝ :=
  fun s x => intervalDomainChemotaxisDiv p (realSlice u_star s)
    (coupledChemicalConcentration p (realSlice u_star) s) x

theorem wChem_lift_eq (p : CM2Params) (u_star : EWA T 1) (s : ℝ) :
    intervalDomainLift (wChem p u_star s)
      = coupledChemDivSourceLift p (realSlice u_star) s := rfl

/-- **The chemDiv realized-source record.**  Carries exactly the analytic atoms of the
committed pointwise eval bridge `evalST_chemDivEWA_eq_coupledChemDivSourceLift`. -/
theorem chemDiv_realizesOn (p : CM2Params) (u_star : EWA T 1)
    (hER_star : EvenRealEWA u_star)
    (hgrad : ∀ (τ : TimeDom T),
      Summable fun k : ℕ =>
        |(intervalNeumannResolverCoeff p (realSlice u_star τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ (τ : TimeDom T), ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (chemFluxEWA p.μ p.ν p.β p.γ p.hμ u_star))
        = ((chemFluxLifted p (realSlice u_star τ.1) y : ℝ) : ℂ))
    (h_flux_diff : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (chemFluxLifted p (realSlice u_star τ.1)) x) :
    EWARealizesOn T 0 (chemDivEWA p.μ p.ν p.γ p.hμ p u_star) (wChem p u_star) := by
  -- even-real of the chemDiv element, per slice
  have hER : EvenRealEWA (chemDivEWA p.μ p.ν p.γ p.hμ p u_star) :=
    chemDivEWA_evenReal FnegEWA_evenReal_Hyp_proved p.hμ p hER_star
  -- pointwise eval on the interior, identified with the realized lift
  have heval : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (x : WA.Circ) (chemDivEWA p.μ p.ν p.γ p.hμ p u_star)
        = ((intervalDomainLift (wChem p u_star τ.1) x : ℝ) : ℂ) := by
    intro τ x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    rw [wChem_lift_eq]
    exact evalST_chemDivEWA_eq_coupledChemDivSourceLift p.hμ p (realSlice u_star) u_star
      τ x hx hxIcc (hgrad τ) (h_flux_nbhd τ) (h_flux_diff τ x hx)
  -- the coefficient identity (non-circular)
  have hcoeff : ∀ (τ : TimeDom T) (k : ℕ),
      ewaCosCoeffAt (chemDivEWA p.μ p.ν p.γ p.hμ p u_star) τ k
        = cosineCoeffs (intervalDomainLift (wChem p u_star τ.1)) k := by
    intro τ k
    exact ewaCosCoeffAt_eq_cosineCoeffs_of_even_real τ
      (fun n => hER.even τ n) (fun n => hER.real τ n) (heval τ) k
  refine
    { eval_eq := ?_, is_cosine_series := ?_, summable_cos := ?_ }
  · -- full-circle eval_eq
    intro τ x
    rw [evalST_incl0_self,
      evalST_eq_cosineSynthesis_of_even_real (fun n => hER.even τ n) (fun n => hER.real τ n) x]
    congr 1
    refine tsum_congr (fun k => ?_)
    rw [hcoeff τ k]
  · -- is_cosine_series on (0,1): lift = synthesis on Ioo (eval bridge).
    -- Weakened from Icc (2026-06-24): chemDiv lift is discontinuous at
    -- endpoints {0,1} due to zero-extension; Ioo agreement is direct.
    intro τ x hx
    have h1 := heval τ x hx
    have h2 := evalST_eq_cosineSynthesis_of_even_real
      (fun n => hER.even τ n) (fun n => hER.real τ n) x
    rw [h2] at h1
    have h3 : (∑' k : ℕ, ewaCosCoeffAt
          (chemDivEWA p.μ p.ν p.γ p.hμ p u_star) τ k
          * cosineMode k x)
        = ∑' k : ℕ, cosineCoeffs
            (intervalDomainLift (wChem p u_star τ.1)) k
          * cosineMode k x :=
      tsum_congr (fun k => by rw [hcoeff τ k])
    rw [h3] at h1
    exact Complex.ofReal_inj.mp h1.symm
  · -- intrinsic summability, congr'd to cosineCoeffs (lift)
    intro τ
    refine (ewaCosCoeffAt_abs_summable (fun n => hER.even τ n)
      (fun n => hER.real τ n)).congr (fun k => ?_)
    rw [hcoeff τ k]

/-! ### The logistic realized-source record. -/

/-- The realized real-space logistic source slice (lift-matches `coupledLogisticSourceLift`
by `rfl`). -/
def wLog (p : CM2Params) (u_star : EWA T 1) :
    ℝ → intervalDomainPoint → ℝ :=
  fun s => intervalLogisticSource p (realSlice u_star s)

theorem wLog_lift_eq (p : CM2Params) (u_star : EWA T 1) (s : ℝ) :
    intervalDomainLift (wLog p u_star s)
      = coupledLogisticSourceLift p (realSlice u_star) s := rfl

/-- **The logistic realized-source record.**  Carries exactly the analytic atoms of the
committed pointwise eval bridge `evalST_growthEWA_eq_logisticLifted`. -/
theorem logistic_realizesOn (p : CM2Params) (u_star : EWA T 1)
    (hER_star : EvenRealEWA u_star)
    (h_u : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) u_star)
        = (intervalDomainLift (realSlice u_star τ.1) x : ℂ))
    (h_uα : ∀ (τ : TimeDom T), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      evalST τ x (GWA.incl (by omega : (0 : ℕ) ≤ 1) (realPowEWA u_star p.α))
        = ((intervalDomainLift (realSlice u_star τ.1) x ^ p.α : ℝ) : ℂ))
    (h_src_cont : ∀ (τ : TimeDom T), Continuous (wLog p u_star τ.1)) :
    EWARealizesOn T 0
      (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b u_star))
      (wLog p u_star) := by
  -- even-real of the grade-dropped growth element
  have hER : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b u_star)) :=
    (growthEWA_evenReal FnegEWA_evenReal_Hyp_proved hER_star).incl (by omega)
  -- pointwise eval on the interior, identified with the realized lift
  have heval : ∀ (τ : TimeDom T), ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b u_star))
        = ((intervalDomainLift (wLog p u_star τ.1) x : ℝ) : ℂ) := by
    intro τ x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    rw [wLog_lift_eq]
    exact evalST_growthEWA_eq_logisticLifted p u_star (realSlice u_star τ.1)
      τ x hxIcc (h_u τ x hxIcc) (h_uα τ x hxIcc)
  -- the coefficient identity (non-circular)
  have hcoeff : ∀ (τ : TimeDom T) (k : ℕ),
      ewaCosCoeffAt (GWA.incl (by omega : (0 : ℕ) ≤ 1) (growthEWA p.α p.a p.b u_star)) τ k
        = cosineCoeffs (intervalDomainLift (wLog p u_star τ.1)) k := by
    intro τ k
    exact ewaCosCoeffAt_eq_cosineCoeffs_of_even_real τ
      (fun n => hER.even τ n) (fun n => hER.real τ n) (heval τ) k
  refine
    { eval_eq := ?_, is_cosine_series := ?_, summable_cos := ?_ }
  · intro τ x
    rw [evalST_incl0_self,
      evalST_eq_cosineSynthesis_of_even_real (fun n => hER.even τ n) (fun n => hER.real τ n) x]
    congr 1
    refine tsum_congr (fun k => ?_)
    rw [hcoeff τ k]
  · intro τ x hx
    set g : ℝ → ℝ := fun y => ∑' k : ℕ,
      cosineCoeffs (intervalDomainLift (wLog p u_star τ.1)) k * cosineMode k y with hg
    have hsum : Summable
        (fun k => |cosineCoeffs (intervalDomainLift (wLog p u_star τ.1)) k|) := by
      refine (ewaCosCoeffAt_abs_summable (fun n => hER.even τ n)
        (fun n => hER.real τ n)).congr (fun k => ?_)
      rw [hcoeff τ k]
    have h1 := heval τ x hx
    have h2 := evalST_eq_cosineSynthesis_of_even_real
      (fun n => hER.even τ n) (fun n => hER.real τ n) x
    rw [h2] at h1
    have h3 : (∑' k : ℕ,
          ewaCosCoeffAt (GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (growthEWA p.α p.a p.b u_star)) τ k * cosineMode k x) = g x := by
      rw [hg]; exact tsum_congr (fun k => by rw [hcoeff τ k])
    rw [h3] at h1
    exact Complex.ofReal_inj.mp h1.symm
  · intro τ
    refine (ewaCosCoeffAt_abs_summable (fun n => hER.even τ n)
      (fun n => hER.real τ n)).congr (fun k => ?_)
    rw [hcoeff τ k]

end ShenWork.EWA
