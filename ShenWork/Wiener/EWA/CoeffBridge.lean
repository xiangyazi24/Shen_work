import Mathlib
import ShenWork.Wiener.EWA.Decisive
import ShenWork.Wiener.WeightedL1CosineEval
import ShenWork.Wiener.WeightedL1CosineAdapter
import ShenWork.PDE.IntervalNeumannFullKernel
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.CosineSpectrum
import ShenWork.PDE.CosineParsevalBridge

/-!
# EWA brick B6 — the coefficient bridge (Phase C join, first join brick)

The committed source package `DuhamelSourceTimeC1On` consumes the Neumann cosine
coefficient family of the source.  This file extracts those coefficients from an
EWA element and proves they equal the committed `cosineCoeffs` of the realized
real-space function.  The eval-realization is taken as a HYPOTHESIS (the eval
bridge B5 supplies instances later).

## Resolution of the even-extension subtlety (spec's "ONE likely subtlety")
`fourierCoeff` integrates over the whole period-`2` circle, while the physical
realization holds on `[0,1]`.  The committed `evalC_ofCosineCoeffs` is stated only
on `Set.Icc 0 1`, so interval agreement alone does NOT pin down the period-`2`
Fourier integral.  We resolve this via **spec option (i)**: `EWARealizesOn.eval_eq`
is stated on the FULL circle (the realized slice IS its even-periodic cosine-series
synthesis).  NOTE for B5 (the eval bridge that discharges `eval_eq`): the committed
`iterate_lift_eq_cosineSeries` is `[0,1]`-restricted and supplies only the
`is_cosine_series` field, NOT the full-circle `eval_eq`.  B5 must additionally prove
the slice-coefficient identity `(sliceWA τ U).toFun = ofCosineCoeffs (cosineCoeffs (lift))`
(equivalently route the realized slice through `evalC_ofCosineCoeffs_all`); that
coefficient-embedding step is B5's real obligation.  The pointwise cosine bridge
`unitIntervalCosine_eq_fourier_pair` is itself unrestricted in `x`, so we re-derive
the FULL-circle synthesis identity `evalC_ofCosineCoeffs_all` here (the committed
`[0,1]` hypothesis is vestigial — its proof never uses `hx`).  Then both circle
functions agree everywhere ⇒ equal Fourier coefficients ⇒ the bridge.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum ShenWork.CosineParsevalBridge
open ShenWork.IntervalNeumannFullKernel ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Full-circle synthesis of even cosine coefficients.

The committed `WA.evalC_ofCosineCoeffs` restricts to `x ∈ Icc 0 1`, but the
underlying pointwise bridge `unitIntervalCosine_eq_fourier_pair` holds for ALL
real `x`.  We re-derive the unrestricted version (needed to equate the two
circle functions everywhere, not just on the interval). -/
theorem evalC_ofCosineCoeffs_all (c : ℕ → ℝ) (hc : Summable (fun k => |c k|)) (x : ℝ) :
    WA.evalC (⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hc)⟩ : WA 0)
        (x : AddCircle (2 : ℝ))
      = ((∑' k : ℕ, c k * cosineMode k x : ℝ) : ℂ) := by
  set a : WA 0 := ⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hc)⟩ with ha
  set g : ℤ → ℂ := fun n => (ofCosineCoeffs c n) • fourier (T := (2:ℝ)) n
      (x : AddCircle (2:ℝ)) with hg
  have hLHS : WA.evalC a (x : AddCircle (2:ℝ)) = ∑' n : ℤ, g n := by
    rw [WA.evalC_apply, WA.evalLin_apply, WA.evalFun,
      ← ContinuousMap.tsum_apply (WA.summable_evalTerm a)]
    exact tsum_congr (fun n => rfl)
  rw [hLHS]
  have hgsum : Summable g := by
    apply Summable.of_norm
    refine (WA.summable_norm_toFun a).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    calc ‖g n‖ = ‖(WA.evalTerm a n) (x : AddCircle (2:ℝ))‖ := rfl
      _ ≤ ‖WA.evalTerm a n‖ := (WA.evalTerm a n).norm_coe_le_norm _
      _ = ‖a.toFun n‖ := WA.norm_evalTerm a n
  have hipos : Function.Injective (fun m : ℕ => (m:ℤ)+1) := by
    intro p q hpq; simpa using hpq
  have hineg : Function.Injective (fun m : ℕ => -((m:ℤ)+1)) := by
    intro p q hpq; simp only [neg_inj, add_left_inj] at hpq; exact_mod_cast hpq
  have hpos : Summable (fun m : ℕ => g ((m:ℤ)+1)) := hgsum.comp_injective hipos
  have hneg : Summable (fun m : ℕ => g (-((m:ℤ)+1))) := hgsum.comp_injective hineg
  have hsplit : (∑' n : ℤ, g n)
      = (∑' m : ℕ, g ((m:ℤ)+1)) + g 0 + ∑' m : ℕ, g (-((m:ℤ)+1)) := by
    have := tsum_of_add_one_of_neg_add_one hpos hneg
    simpa using this
  rw [hsplit]
  -- collapse each ±(m+1) pair to a cos term via the (unrestricted) bridge
  have hpair : ∀ m : ℕ, g ((m:ℤ)+1) + g (-((m:ℤ)+1))
      = ((c (m+1) : ℝ) : ℂ) * cosineMode (m+1) x := by
    intro m
    have hval : ofCosineCoeffs c ((m:ℤ)+1) = ((c (m+1) : ℝ) / 2 : ℂ) := by
      unfold ofCosineCoeffs; rw [if_neg (by omega)]
      have : ((m:ℤ)+1).natAbs = m+1 := by omega
      rw [this]
    have hbridge := unitIntervalCosine_eq_fourier_pair (m+1) x
    have hcast : ((m:ℤ)+1 : ℤ) = ((m+1 : ℕ) : ℤ) := by push_cast; ring
    change (ofCosineCoeffs c ((m:ℤ)+1)) • fourier (T := (2:ℝ)) ((m:ℤ)+1)
            (x : AddCircle (2:ℝ))
        + (ofCosineCoeffs c (-((m:ℤ)+1))) • fourier (T := (2:ℝ)) (-((m:ℤ)+1))
            (x : AddCircle (2:ℝ))
        = ((c (m+1) : ℝ) : ℂ) * cosineMode (m+1) x
    rw [ofCosineCoeffs_neg, hval, smul_eq_mul, smul_eq_mul, cosineMode, hcast, hbridge]
    push_cast; ring
  have hpairsum : (∑' m : ℕ, g ((m:ℤ)+1)) + ∑' m : ℕ, g (-((m:ℤ)+1))
      = ∑' m : ℕ, ((c (m+1) : ℝ) : ℂ) * cosineMode (m+1) x := by
    rw [← hpos.tsum_add hneg]; exact tsum_congr hpair
  have hg0 : g 0 = ((c 0 : ℝ) : ℂ) * cosineMode 0 x := by
    simp only [hg, smul_eq_mul]
    have : ofCosineCoeffs c 0 = (c 0 : ℂ) := by unfold ofCosineCoeffs; rw [if_pos rfl]
    rw [this, cosineMode]; simp
  rw [show (∑' m : ℕ, g ((m:ℤ)+1)) + g 0 + ∑' m : ℕ, g (-((m:ℤ)+1))
        = ((∑' m : ℕ, g ((m:ℤ)+1)) + ∑' m : ℕ, g (-((m:ℤ)+1))) + g 0 by ring,
      hpairsum, hg0]
  have hcs : Summable (fun k : ℕ => ((c k : ℝ) : ℂ) * cosineMode k x) := by
    apply Summable.of_norm
    refine (hc.mul_right 1).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    rw [norm_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hcos : ‖((cosineMode k x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, cosineMode]; exact Real.abs_cos_le_one _
    calc |c k| * ‖((cosineMode k x : ℝ) : ℂ)‖ ≤ |c k| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      _ = |c k| := by ring
  have hRHS : ((∑' k : ℕ, c k * cosineMode k x : ℝ) : ℂ)
      = ∑' k : ℕ, ((c k : ℝ) : ℂ) * cosineMode k x := by
    rw [Complex.ofReal_tsum]; exact tsum_congr (fun k => by push_cast; ring)
  rw [hRHS, hcs.tsum_eq_zero_add]; ring

/-! ### 1. The realization predicate (B5 supplies instances). -/

/-- The realized EWA slice equals its even-periodic Neumann cosine-series synthesis
on the FULL circle (spec option (i); TRUE for committed `picardIter` lifts), with
the interval form recorded separately and the coefficients summable. -/
structure EWARealizesOn (T : ℝ) (r : ℕ) (U : EWA T r)
    (w : ℝ → intervalDomainPoint → ℝ) : Prop where
  /-- Full-circle realization: the slice synthesis is the cosine series everywhere. -/
  eval_eq : ∀ (τ : TimeDom T) (x : ℝ),
    evalST τ (x : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ r) U)
      = ((∑' k : ℕ, cosineCoeffs (intervalDomainLift (w τ.1)) k * cosineMode k x : ℝ) : ℂ)
  /-- Interval form: on `(0,1)` the cosine series reproduces the physical lift.
  Weakened from `Icc` to `Ioo` (2026-06-24): the chemotaxis-divergence source
  uses `deriv` of a zero-extension lift, which is discontinuous at endpoints
  `{0,1}` (left-derivative = 0, interior right-limit ≠ 0).  No consumer
  projects this field, and the interior agreement suffices for all downstream
  cosine-coefficient identities. -/
  is_cosine_series : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0:ℝ) 1 →
    intervalDomainLift (w τ.1) x
      = ∑' k : ℕ, cosineCoeffs (intervalDomainLift (w τ.1)) k * cosineMode k x
  /-- The realized coefficient family is absolutely summable. -/
  summable_cos : ∀ τ : TimeDom T,
    Summable (fun k => |cosineCoeffs (intervalDomainLift (w τ.1)) k|)

/-! ### 2. The cosine-coefficient extractor from an EWA element. -/

/-- Extract the `k`-th Neumann cosine coefficient from an EWA source slice as a
sum of `±`-modes (no evenness needed at the envelope stage). -/
noncomputable def ewaCosCoeffAt (F : EWA T 0) (τ : TimeDom T) (k : ℕ) : ℝ :=
  if k = 0 then ((sliceWA τ F).toFun 0).re
  else (((sliceWA τ F).toFun (k : ℤ) + (sliceWA τ F).toFun (-(k : ℤ))).re)

/-! ### 3. THE BRIDGE LEMMA. -/

/-- **The coefficient bridge.**  The `±`-mode extractor of an EWA source slice
equals the committed Neumann cosine coefficient of its realized real-space
function. -/
theorem ewaCosCoeffAt_eq_cosineCoeffs_of_eval {T : ℝ} {U : EWA T 0}
    {w : ℝ → intervalDomainPoint → ℝ} (H : EWARealizesOn T 0 U w)
    (τ : TimeDom T) (k : ℕ) :
    ewaCosCoeffAt U τ k = cosineCoeffs (intervalDomainLift (w τ.1)) k := by
  set c : ℕ → ℝ := cosineCoeffs (intervalDomainLift (w τ.1)) with hc_def
  have hcsum : Summable (fun k => |c k|) := H.summable_cos τ
  set a' : WA 0 :=
    ⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hcsum)⟩ with ha'
  -- the two circle functions agree everywhere
  have hfun : (fun x : WA.Circ => WA.evalC (sliceWA τ U) x)
      = (fun x : WA.Circ => WA.evalC a' x) := by
    funext y
    induction y using QuotientAddGroup.induction_on with
    | _ x =>
      have hL : WA.evalC (sliceWA τ U) ((x : ℝ) : WA.Circ)
          = ((∑' k : ℕ, c k * cosineMode k x : ℝ) : ℂ) := by
        have := H.eval_eq τ x
        rw [evalST_apply, WA.evalAt_apply] at this
        have hslice : sliceWA τ (GWA.incl (by omega : (0:ℕ) ≤ 0) U) = sliceWA τ U := by
          apply WA.ext
          funext n
          rw [coeff_sliceWA, coeff_sliceWA, GWA.incl_toFun]
        rw [hslice] at this
        rw [WA.evalC_apply]; exact this
      have hR : WA.evalC a' ((x : ℝ) : WA.Circ)
          = ((∑' k : ℕ, c k * cosineMode k x : ℝ) : ℂ) := by
        rw [ha']; exact evalC_ofCosineCoeffs_all c hcsum x
      change WA.evalC (sliceWA τ U) ((x : ℝ) : WA.Circ) = WA.evalC a' ((x : ℝ) : WA.Circ)
      rw [hL, hR]
  -- equal functions ⇒ equal Fourier coefficients ⇒ equal coefficients
  have hcoeff : ∀ n : ℤ, (sliceWA τ U).toFun n = ofCosineCoeffs c n := by
    intro n
    have h1 := WA.fourierCoeff_evalC_eq_coeff (sliceWA τ U) n
    have h2 := WA.fourierCoeff_evalC_eq_coeff a' n
    rw [hfun, h2] at h1
    exact h1.symm
  -- read off the k = 0 and k ≥ 1 cases
  unfold ewaCosCoeffAt
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, hcoeff 0]
    have : ofCosineCoeffs c 0 = (c 0 : ℂ) := by unfold ofCosineCoeffs; rw [if_pos rfl]
    rw [this, Complex.ofReal_re]
  · rw [if_neg hk, hcoeff (k : ℤ), hcoeff (-(k : ℤ)), ofCosineCoeffs_neg]
    have hval : ofCosineCoeffs c (k : ℤ) = ((c k : ℝ) / 2 : ℂ) := by
      unfold ofCosineCoeffs
      rw [if_neg (by exact_mod_cast hk)]
      have : ((k : ℤ)).natAbs = k := Int.natAbs_natCast k
      rw [this]
    rw [hval, show ((c k : ℝ) / 2 : ℂ) + ((c k : ℝ) / 2 : ℂ) = ((c k : ℝ) : ℂ) by
      ring, Complex.ofReal_re]

end ShenWork.EWA
