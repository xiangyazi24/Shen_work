/-
  ShenWork/Paper2/IntervalCarrySeamDischarge.lean

  χ₀<0 — discharge the FOUR per-slice seam BRIDGES of `CarrySeam`
  (`hbr`/`hbridge`/`hvrel`/`hdiv`) from MILD regularity, assembling a GENUINE
  `CarrySeam` inhabitant `carrySeam_of_mild`.

  ## Honest accounting of the four bridges

  * `hdiv` (the divergence-mode SINE identity `|sineCoeffs (vx τ) k|
    = √λ_k·|cosineCoeffs (v τ) k|`, with `vx τ = ∂ₓ(v τ)`): BUILT here.  The landed
    divergence identity (`cosineCoeffs_deriv_eq_sqrtLambda_sineCoeff`) is the COSINE
    direction for a Dirichlet-vanishing flux; the SINE direction is its dual and is
    genuinely absent, so it is built from the raw sine-IBP
    `∫ Q'·sin(kπx) = −kπ·∫ Q·cos(kπx)` whose boundary term `[sin(kπ·)·Q]₀¹` vanishes
    AUTOMATICALLY (`sin 0 = sin(kπ) = 0`), needing NO boundary condition on `v`.

  * `hvrel` (the resolver relay `Envelopes (resolverCoeff 1 E.env) (cosineCoeffs (v τ))`):
    DISCHARGED here.  With the resolver MODEL `v τ = resolverValue μ (cosineCoeffs
    (lift (u τ)))` (carried `hvdef`), the LANDED Fourier coefficient recovery
    `cosineCoeffs_of_l1_cosineSeries` gives the DIAGONAL identity `cosineCoeffs (v τ) k
    = resolverCoeff μ (cosineCoeffs (lift (u τ))) k`; `envelopes_resolver` lifts the
    `E.hdom` envelope through the resolver, and `1 ≤ μ` (carried `hμ1`) collapses
    `resolverCoeff μ E.env` to `resolverCoeff 1 E.env`.

  * `hbr` (`CosineMulBridge (lift (u τ)) (denom factor)`): CONSUMED — the LANDED
    `cosineMulBridge_of_summable` (continuity + reflCircle ℓ¹ of each factor), NOT
    re-proved.

  * `hbridge` (`MixedMulBridge (W τ) (vx τ)`, the SINE-output product interchange):
    no landed discharger exists (only its envelope-monotone CONSEQUENCES are landed;
    the analytic sin×cos×cos interchange `mixedMulBridge_of_summable` is genuinely
    absent from the repo).  It is therefore CARRIED as the EXPLICIT, PRECISELY-NAMED
    atom `hmixbridge` — never faked, never weakening `CarrySeam`.

  The remaining fields (`hû₀`, scalar params, `hvnn`, `hQ`/`hWdef`, `hQ_cont`/`L`/
  `hFl_cont`) pass through honestly as carried mild/definitional data.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalChiNegSeamFixedReach
import ShenWork.Paper2.IntervalDivergenceModeIdentity
import ShenWork.Paper2.IntervalEnvelopeProp
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.Paper2.IntervalWienerAlgebraResidual

noncomputable section

namespace ShenWork.Paper2.IntervalCarrySeamDischarge

open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCosineInversion (reflCircle)
open ShenWork.Paper2.HSigmaScale (lam lam_nonneg MemHSigma resolverCoeff)
open ShenWork.Paper2.IntervalDivergenceModeIdentity
  (sineCoeffs sineCoeffs_zero sineCoeffs_pos sqrt_lam_eq_kpi)
open ShenWork.Paper2.IntervalEnvelopeProp (Envelopes envelopes_resolver)
open ShenWork.Paper2.IntervalDenomEnvelopeResolver (resolverValue)
open ShenWork.Paper2.IntervalWienerAlgebra
  (CosineMulBridge cosineMulBridge_of_summable hSigma_subset_l1_of_gt_half)
open ShenWork.Paper2.IntervalMixedProduct (MixedMulBridge)
open ShenWork.IntervalPicardIterateRestart (cosineCoeffs_of_l1_cosineSeries)
open ShenWork.Paper2.IntervalChiNegSeamFixedReach (CarrySeam)

/-! ## Bridge `hdiv` — the SINE-of-derivative spectral identity (BUILT). -/

/-- `HasDerivAt (x ↦ sin(kπx)) (kπ·cos(kπx)) x`. -/
theorem hasDerivAt_sin_kpi (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin ((k : ℝ) * Real.pi * y))
      ((k : ℝ) * Real.pi * Real.cos ((k : ℝ) * Real.pi * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => (k : ℝ) * Real.pi * y)
      ((k : ℝ) * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) * Real.pi)
  have hcomp : HasDerivAt (fun y : ℝ => Real.sin ((k : ℝ) * Real.pi * y))
      (Real.cos ((k : ℝ) * Real.pi * x) * ((k : ℝ) * Real.pi)) x :=
    (Real.hasDerivAt_sin ((k : ℝ) * Real.pi * x)).comp x hinner
  convert hcomp using 1; ring

/-- **Raw sine-IBP identity.**  For `v` with derivative `vx` on `[0,1]` and `vx`
integrable: `∫₀¹ vx·sin(kπx) = −kπ·∫₀¹ v·cos(kπx)`.  The boundary term
`[sin(kπ·)·v]₀¹ = sin(kπ)·v 1 − sin 0·v 0 = 0` vanishes automatically — NO boundary
condition on `v` is needed. -/
theorem rawSinCoeff_deriv_eq_neg_kpi_rawCosCoeff
    {v vx : ℝ → ℝ} (k : ℕ)
    (hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt v (vx x) x)
    (hvxint : IntervalIntegrable vx MeasureTheory.volume 0 1) :
    (∫ x in (0 : ℝ)..1, vx x * Real.sin ((k : ℝ) * Real.pi * x))
      = -((k : ℝ) * Real.pi) *
          ∫ x in (0 : ℝ)..1, v x * Real.cos ((k : ℝ) * Real.pi * x) := by
  set s : ℝ → ℝ := fun y => Real.sin ((k : ℝ) * Real.pi * y) with hs_def
  set s' : ℝ → ℝ := fun y => (k : ℝ) * Real.pi * Real.cos ((k : ℝ) * Real.pi * y)
    with hs'_def
  have hs : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt s (s' x) x :=
    fun x _ => hasDerivAt_sin_kpi k x
  have hs'_int : IntervalIntegrable s' MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hs hv hs'_int hvxint
  have hs0 : s 0 = 0 := by simp [hs_def]
  have hs1 : s 1 = 0 := by
    simp only [hs_def, mul_one]; exact Real.sin_nat_mul_pi k
  rw [hs0, hs1] at hibp
  simp only [zero_mul, sub_zero, zero_sub] at hibp
  have hcomm : (∫ x in (0 : ℝ)..1, vx x * s x)
      = ∫ x in (0 : ℝ)..1, s x * vx x := by
    refine intervalIntegral.integral_congr (fun x _ => ?_); ring
  rw [hcomm, hibp, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [hs'_def]; ring

/-- **The divergence-mode SINE identity (BUILT).**  For `v` with derivative `vx`
on `[0,1]` and `vx` continuous: `|sineCoeffs vx k| = √(lam k)·|cosineCoeffs v k|`,
i.e. the spectral content of `vx = ∂ₓv` in the SINE basis. -/
theorem abs_sineCoeffs_deriv_eq_sqrtLambda_abs_cosineCoeff
    {v vx : ℝ → ℝ} (k : ℕ)
    (hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt v (vx x) x)
    (hvxcont : Continuous vx) :
    |sineCoeffs vx k| = Real.sqrt (lam k) * |cosineCoeffs v k| := by
  have hvxint : IntervalIntegrable vx MeasureTheory.volume 0 1 :=
    hvxcont.intervalIntegrable 0 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [sineCoeffs_zero, sqrt_lam_eq_kpi]; simp
  · have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [sineCoeffs_pos hkne, sqrt_lam_eq_kpi,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_pos_eq_integral hkne]
    have hraw := rawSinCoeff_deriv_eq_neg_kpi_rawCosCoeff k hv hvxint
    have hcommS : (∫ x in (0 : ℝ)..1, Real.sin ((k : ℝ) * Real.pi * x) * vx x)
        = ∫ x in (0 : ℝ)..1, vx x * Real.sin ((k : ℝ) * Real.pi * x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    have hcommC : (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * v x)
        = ∫ x in (0 : ℝ)..1, v x * Real.cos ((k : ℝ) * Real.pi * x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    rw [hcommS, hraw, hcommC, abs_mul, abs_mul, abs_mul, abs_neg]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) * Real.pi := by positivity
    rw [abs_of_nonneg hk0, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; ring

/-! ## Bridge `hvrel` — the resolver relay (DISCHARGED via the diagonal identity). -/

/-- **The resolver DIAGONAL identity.**  Since `resolverValue μ g x
= ∑'_k resolverCoeff μ g k · cosineMode k x` (definitionally) and the resolver
coefficients are `ℓ¹` (`hsum`), the LANDED Fourier coefficient recovery
`cosineCoeffs_of_l1_cosineSeries` gives `cosineCoeffs (resolverValue μ g) k
= resolverCoeff μ g k`. -/
theorem cosineCoeffs_resolverValue_eq_resolverCoeff {μ : ℝ} {g : ℕ → ℝ}
    (hsum : Summable (fun k => |resolverCoeff μ g k|)) (k : ℕ) :
    cosineCoeffs (resolverValue μ g) k = resolverCoeff μ g k := by
  have h : cosineCoeffs (fun x => ∑' j, resolverCoeff μ g j * cosineMode j x) k
      = resolverCoeff μ g k := cosineCoeffs_of_l1_cosineSeries hsum k
  exact h

/-- **The resolver relay `hvrel`, DISCHARGED.**  From the envelope `henv`
(`Envelopes E.env (cosineCoeffs (lift (u τ)))`, supplied by `E.hdom`), the resolver
model `hvdef`, the resolver coefficient `ℓ¹` `hsum`, and `1 ≤ μ` (`hμ1`):
`Envelopes (resolverCoeff 1 E.env) (cosineCoeffs (v τ))`.  Chain: lift the envelope
through `envelopes_resolver` (μ), rewrite `cosineCoeffs (v τ)` to `resolverCoeff μ`
via the diagonal identity, then `μ+λ_k ≥ 1+λ_k` collapses `resolverCoeff μ E.env` to
`resolverCoeff 1 E.env`. -/
theorem hvrel_of_mild {μ : ℝ} {env g : ℕ → ℝ} {vτ : ℝ → ℝ}
    (hμ : 0 < μ) (hμ1 : 1 ≤ μ)
    (henv : Envelopes env g)
    (hsum : Summable (fun k => |resolverCoeff μ env k|))
    (hvdef : vτ = resolverValue μ g) :
    Envelopes (resolverCoeff 1 env) (cosineCoeffs vτ) := by
  intro k
  have hres : Envelopes (resolverCoeff μ env) (resolverCoeff μ g) :=
    envelopes_resolver hμ henv
  have hsumg : Summable (fun j => |resolverCoeff μ g j|) := by
    refine hsum.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => ?_)
    unfold resolverCoeff
    have hden : 0 < μ + lam j := by have := lam_nonneg j; linarith
    have henv0 : 0 ≤ env j := le_trans (abs_nonneg _) (henv j)
    rw [abs_div, abs_div, abs_of_pos hden, abs_of_nonneg henv0]
    gcongr
    exact henv j
  have hdiag : cosineCoeffs vτ k = resolverCoeff μ g k := by
    rw [hvdef]; exact cosineCoeffs_resolverValue_eq_resolverCoeff hsumg k
  rw [hdiag]
  refine le_trans (hres k) ?_
  unfold resolverCoeff
  have hlam := lam_nonneg k
  have hd1 : 0 < 1 + lam k := by linarith
  have hdμ : 0 < μ + lam k := by linarith
  have henv0 : 0 ≤ env k := le_trans (abs_nonneg _) (henv k)
  apply div_le_div_of_nonneg_left henv0 hd1
  linarith

/-! ## The genuine `CarrySeam` inhabitant. -/

variable {p : CM2Params} {μ β t σ : ℝ}
variable {u : ℝ → intervalDomainPoint → ℝ} {v vx W : ℝ → ℝ → ℝ}

/-- **`carrySeam_of_mild` — a GENUINE `CarrySeam` inhabitant with `hdiv`/`hvrel`
DISCHARGED and `hbr` CONSUMED.**  The only bridge carried is `hbridge` (the
sine-output product interchange `hmixbridge`, genuinely absent from the repo).  The
two extra non-mild facts are the resolver model `hvdef` and `1 ≤ μ` (`hμ1`); all
other inputs are mild regularity / definitional. -/
def carrySeam_of_mild
    (E : ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ => cosineCoeffs (intervalDomainLift (u τ))))
    (hμ : 0 < μ) (hμ1 : 1 ≤ μ) (hσ0 : 1 / 2 < σ) (hσ1 : σ < 3 / 2)
    (hβ : 0 ≤ β) (ht : 0 < t) (ht1 : t ≤ 1)
    (hû₀ : MemHSigma (σ + 1 / 4) (cosineCoeffs (intervalDomainLift (u 0))))
    (hvnn : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x,
      0 ≤ resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x)
    (hQ : ∀ τ, ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ
      = fun x => W τ x * vx τ x)
    (hWdef : ∀ τ, W τ = fun x => intervalDomainLift (u τ) x
      * (1 + resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))
    -- `hbr` inputs (mild): continuity + reflCircle ℓ¹ of each cosine factor.
    (hu_cont : ∀ τ ∈ Set.Icc (0:ℝ) t, Continuous (intervalDomainLift (u τ)))
    (hwfac_cont : ∀ τ ∈ Set.Icc (0:ℝ) t, Continuous (fun x => (1 + resolverValue μ
      (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β)))
    (hu_sum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (intervalDomainLift (u τ))) n))
    (hwfac_sum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun n : ℤ => fourierCoeff (reflCircle (fun x => (1 + resolverValue μ
        (cosineCoeffs (intervalDomainLift (u τ))) x) ^ (-β))) n))
    -- `hbridge` carried atom (no landed discharger): the sine-output interchange.
    (hmixbridge : ∀ τ ∈ Set.Icc (0:ℝ) t, MixedMulBridge (W τ) (vx τ))
    -- `hvrel` inputs (mild + resolver model): resolver model + ℓ¹ of resolver coeffs.
    (hvdef : ∀ τ, v τ = resolverValue μ (cosineCoeffs (intervalDomainLift (u τ))))
    (hvsum : ∀ τ ∈ Set.Icc (0:ℝ) t,
      Summable (fun k => |resolverCoeff μ E.env k|))
    -- `hdiv` inputs (mild C¹): `vx τ = ∂ₓ(v τ)` with `vx τ` continuous.
    (hvderiv : ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (v τ) (vx τ x) x)
    (hvxcont : ∀ τ ∈ Set.Icc (0:ℝ) t, Continuous (vx τ))
    -- passthrough continuity/envelope data.
    (hQ_cont : ∀ k, Continuous (fun τ => sineCoeffs
      (ShenWork.Paper2.IntervalDecompTauLift.conjQ p u τ) k))
    (L : ShenWork.Paper2.IntervalTrajectoryEnvelope.TrajectoryHSigmaEnvelope σ t
      (fun τ k => ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k τ))
    (hFl_cont : ∀ k, Continuous (ShenWork.Paper2.IntervalDecompTauLift.conjFl p u k)) :
    CarrySeam p μ β t u v vx W σ E where
  hμ := hμ
  hσ0 := hσ0
  hσ1 := hσ1
  hβ := hβ
  ht := ht
  ht1 := ht1
  hû₀ := hû₀
  hvnn := hvnn
  hQ := hQ
  hWdef := hWdef
  hbr := fun τ hτ => cosineMulBridge_of_summable (hu_cont τ hτ) (hwfac_cont τ hτ)
    (hu_sum τ hτ) (hwfac_sum τ hτ)
  hbridge := hmixbridge
  hvrel := fun τ hτ => hvrel_of_mild hμ hμ1
    (fun k => E.hdom τ hτ k) (hvsum τ hτ) (hvdef τ)
  hdiv := fun τ hτ k =>
    abs_sineCoeffs_deriv_eq_sqrtLambda_abs_cosineCoeff k (hvderiv τ hτ) (hvxcont τ hτ)
  hQ_cont := hQ_cont
  L := L
  hFl_cont := hFl_cont

end ShenWork.Paper2.IntervalCarrySeamDischarge

namespace ShenWork.Paper2.IntervalCarrySeamDischarge
section AxiomAudit
#print axioms abs_sineCoeffs_deriv_eq_sqrtLambda_abs_cosineCoeff
#print axioms hvrel_of_mild
#print axioms carrySeam_of_mild
end AxiomAudit
end ShenWork.Paper2.IntervalCarrySeamDischarge
