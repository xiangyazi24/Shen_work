import Mathlib
import ShenWork.Wiener.EWA.CoeffBridge
import ShenWork.Wiener.EWA.ParityFoundations
import ShenWork.Wiener.EWA.SourceEnvelope
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.Paper2.IntervalMildPicardRegularity

/-!
# EWA brick — the NON-CIRCULAR coefficient bridge (Phase C endgame assembly)

This is the assembly piece that discharges the circular `summable_cos` field of
`EWARealizesOn`.  Given an EWA element `F : EWA T 0` that is, at a fixed time `τ`,
**even** and **real** in its ℤ-bilateral coefficients, and whose space-time
synthesis equals a real function `f` on the open interior `(0,1)`, we prove

  `ewaCosCoeffAt F τ k = cosineCoeffs f k`.

The summability needed for the full-circle synthesis (`evalC_ofCosineCoeffs_all`)
is supplied **INTRINSICALLY** from the EWA element's own ℓ¹ membership
(`summable_abs_of_slice_eq`, from `F.mem`), NOT assumed as a hypothesis — that is
the whole point of the "non-circular" qualifier.

## Proof chain
1. `c k := ewaCosCoeffAt F τ k`.
2. **Crux (parity → embedding).** `heven` + `hreal` force the slice coefficients to
   be exactly the even real embedding: `(sliceWA τ F).toFun = ofCosineCoeffs c`.
3. **Intrinsic summability.** `Summable |c|` from `summable_abs_of_slice_eq`
   (`F.mem`), with no `Summable` hypothesis.
4. **Full-circle synthesis.** `evalC_ofCosineCoeffs_all` (summable `c`) gives
   `evalST τ x F = ∑' c_k cosineMode k x` for ALL `x`.
5. **Interior agreement → cosineCoeffs.** From `heval` on `(0,1)`,
   `f = ∑' c_k cosineMode k ·` a.e. on the integration interval, so
   `cosineCoeffs f k = cosineCoeffs (∑' c_j cos) k = c k` via the committed
   `cosineCoeffs_of_l1_cosineSeries`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalNeumannFullKernel ShenWork.IntervalPicardIterateRestart
open ShenWork.IntervalMildPicardRegularity
open ShenWork.Paper2

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-! ### Step 2 — the parity crux: the slice IS the even real embedding. -/

/-- A complex number with zero imaginary part equals the cast of its real part. -/
private theorem ofReal_re_of_im_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [h]

/-- **The parity crux.**  If, at time `τ`, the EWA coefficient family is even
(`heven`) and real (`hreal`), then it is exactly the even real embedding
`ofCosineCoeffs (ewaCosCoeffAt F τ)`. -/
theorem slice_eq_ofCosineCoeffs_of_even_real {F : EWA T 0} {τ : TimeDom T}
    (heven : ∀ n : ℤ, (sliceWA τ F).toFun (-n) = (sliceWA τ F).toFun n)
    (hreal : ∀ n : ℤ, ((sliceWA τ F).toFun n).im = 0) :
    (sliceWA τ F).toFun = ofCosineCoeffs (ewaCosCoeffAt F τ) := by
  set c : ℕ → ℝ := ewaCosCoeffAt F τ with hc
  funext n
  -- It suffices to match real parts (both sides have zero imaginary part).
  have him : (ofCosineCoeffs c n).im = 0 := ofCosineCoeffs_im c n
  rw [ofReal_re_of_im_zero (hreal n), ofReal_re_of_im_zero him]
  congr 1
  rcases eq_or_ne n 0 with hzero | hne
  · subst hzero
    rw [re_ofCosineCoeffs_zero, hc]
    unfold ewaCosCoeffAt; rw [if_pos rfl]
  · -- n ≠ 0 : let k = n.natAbs ≠ 0.  The slice at ±k is even, so c k = 2·(toFun k).re.
    set k : ℕ := n.natAbs with hk
    have hkpos : k ≠ 0 := by rw [hk]; exact Int.natAbs_ne_zero.mpr hne
    -- The embedding real part at n is c k / 2.
    rw [re_ofCosineCoeffs, if_neg hne, ← hk]
    -- c k = (toFun k + toFun(-k)).re; evenness ⇒ = 2·(toFun k).re.
    have hck : c k = ((sliceWA τ F).toFun (k : ℤ)
        + (sliceWA τ F).toFun (-(k : ℤ))).re := by
      rw [hc]; unfold ewaCosCoeffAt; rw [if_neg hkpos]
    rw [hck, heven (k : ℤ), Complex.add_re]
    -- Goal: (toFun n).re = ((toFun k).re + (toFun k).re) / 2.
    -- toFun n = toFun (±k): if n ≥ 0 then n = k, else n = -k and evenness.
    have htn : (sliceWA τ F).toFun n = (sliceWA τ F).toFun (k : ℤ) := by
      rcases le_or_gt 0 n with hpos | hneg
      · rw [hk, Int.natAbs_of_nonneg hpos]
      · have : n = -(k : ℤ) := by
          rw [hk, Int.natCast_natAbs, abs_of_neg hneg]; ring
        rw [this, heven (k : ℤ)]
    rw [htn]; ring

/-! ### Step 5 helper — interior agreement transfers cosineCoeffs. -/

/-- If two real functions agree on the open interior `(0,1)`, their Neumann cosine
coefficients agree (the defining interval integral over `(0,1)` ignores the null
endpoint set). -/
theorem cosineCoeffs_congr_on_Ioo {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Ioo (0:ℝ) 1, f x = g x) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  rw [cosineCoeffs_eq_factor_mul_integral, cosineCoeffs_eq_factor_mul_integral]
  congr 1
  apply intervalIntegral.integral_congr_ae
  -- a.e. on `uIoc 0 1`, agreement on `Ioo 0 1` suffices (endpoint `{1}` is null).
  rw [MeasureTheory.ae_iff]
  -- The bad set is contained in `{1}`, which is null.
  apply MeasureTheory.measure_mono_null (t := ({(1:ℝ)} : Set ℝ)) _ (by simp)
  intro x hx
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨hmem, hfail⟩ := hx
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hmem
  simp only [Set.mem_singleton_iff]
  by_contra hx1
  exact hfail (by rw [hfg x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx1⟩])

/-! ### THE NON-CIRCULAR COEFFICIENT BRIDGE. -/

/-- **The non-circular coefficient bridge.**  For an even-real EWA element `F` whose
space-time synthesis realizes the real function `f` on the interior `(0,1)`, the
`±`-mode cosine extractor recovers the committed Neumann cosine coefficient of `f`.
Summability is INTRINSIC (from `F.mem`); there is no `Summable` hypothesis. -/
theorem ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
    {F : EWA T 0} {f : ℝ → ℝ} (τ : TimeDom T)
    (heven : ∀ n : ℤ, (sliceWA τ F).toFun (-n) = (sliceWA τ F).toFun n)
    (hreal : ∀ n : ℤ, ((sliceWA τ F).toFun n).im = 0)
    (heval : ∀ x ∈ Set.Ioo (0:ℝ) 1, evalST τ (x : WA.Circ) F = ((f x : ℝ) : ℂ))
    (k : ℕ) :
    ewaCosCoeffAt F τ k = cosineCoeffs f k := by
  -- Step 1–2: the slice is the even real embedding of c.
  set c : ℕ → ℝ := ewaCosCoeffAt F τ with hc
  have hslice : (sliceWA τ F).toFun = ofCosineCoeffs c :=
    slice_eq_ofCosineCoeffs_of_even_real heven hreal
  -- Step 3: INTRINSIC summability (from F.mem, not assumed).
  have hcsum : Summable (fun k : ℕ => |c k|) := summable_abs_of_slice_eq hslice
  -- Step 4: full-circle synthesis equals the cosine series everywhere.
  have hsynth : ∀ x : ℝ,
      evalST τ (x : WA.Circ) F = ((∑' j : ℕ, c j * cosineMode j x : ℝ) : ℂ) := by
    intro x
    set a' : WA 0 := ⟨ofCosineCoeffs c, memW_ofCosineCoeffs (r := 0) (by simpa using hcsum)⟩
      with ha'
    have hsliceWA : sliceWA τ F = a' := by
      apply WA.ext; rw [ha']; exact hslice
    rw [evalST_apply, WA.evalAt_apply, ← WA.evalC_apply, hsliceWA, ha']
    exact evalC_ofCosineCoeffs_all c hcsum x
  -- Step 5: on (0,1), f equals the cosine series; transfer cosineCoeffs.
  have hagree : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      f x = ∑' j : ℕ, c j * cosineMode j x := by
    intro x hx
    have h1 := heval x hx
    rw [hsynth x] at h1
    exact (Complex.ofReal_inj.mp h1.symm)
  -- cosineCoeffs f = cosineCoeffs (synthesis) = c.
  rw [cosineCoeffs_congr_on_Ioo hagree k, cosineCoeffs_of_l1_cosineSeries hcsum k]

end ShenWork.EWA

#print axioms ShenWork.EWA.ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
