import ShenWork.PDE.IntervalSemigroupUniform
import ShenWork.PDE.IntervalFullKernelSourceIBP

/-!
# Conditional C1 approximate identity for the homogeneous initial leg

This module isolates the easy metric part of the homogeneous C1 initial
approach.  The real analytic input, a derivative-commutation/IBP theorem for
the full Neumann semigroup, is kept as an explicit hypothesis.
-/

open MeasureTheory Filter Topology
open scoped Topology

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

namespace ShenWork.IntervalSemigroupC1ApproxIdentity

noncomputable section

/-- The full Neumann semigroup only reads the source on `[0,1]`. -/
theorem intervalFullSemigroupOperator_congr_on_Icc
    {f g : ℝ → ℝ}
    (hfg : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = g y)
    (t x : ℝ) :
    intervalFullSemigroupOperator t f x =
      intervalFullSemigroupOperator t g x := by
  unfold intervalFullSemigroupOperator
  apply MeasureTheory.integral_congr_ae
  have hmem : ∀ᵐ y ∂(intervalMeasure 1), y ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, intervalSet]
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun y hy => hy)
  filter_upwards [hmem] with y hy
  rw [hfg y hy]

/-- Uniform value approximate identity on `[0,1]` for a candidate derivative
profile. -/
def InitialLegDerivativeValueApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalFullSemigroupOperator t df x - df x| < ε

/-- Explicit derivative-commutation/IBP hypothesis for the homogeneous initial
leg.  This is the analytic theorem still missing from the current source-side
toolbox. -/
def InitialLegDerivativeCommutes (f df : ℝ → ℝ) : Prop :=
  ∀ {t : ℝ}, 0 < t → ∀ x ∈ Set.Icc (0 : ℝ) 1,
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x =
      intervalFullSemigroupOperator t df x

/-- Uniform approximate identity on `[0,1]` for the conjugate-kernel
representation of the homogeneous initial-leg derivative.  This is the
remaining analytic input after applying source-side kernel IBP. -/
def InitialLegConjugateDerivativeApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x| < ε

/-- Oscillation part of the conjugate-kernel approximate identity: the kernel
applied to `df y - df x` tends uniformly to zero. -/
def InitialLegConjugateOscillationControl (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)| < ε

/-- Mass-defect part of the conjugate-kernel approximate identity, weighted by
`df x`.  This is where the endpoint compatibility `df 0 = 0` and `df 1 = 0`
matters for the closed interval. -/
def InitialLegConjugateMassDefectControl (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |df x * (-(∫ y in (0 : ℝ)..1,
          intervalNeumannConjugateKernel t x y) - 1)| < ε

/-- Interior-strip version of the conjugate-kernel approximate identity.  The
endpoint boundary layer is deliberately excluded; this is the part expected
from the standard Dirichlet heat-kernel approximate identity away from the
absorbing endpoints. -/
def InitialLegConjugateDerivativeInteriorApprox (df : ℝ → ℝ) : Prop :=
  ∀ η, 0 < η → η < (1 / 2 : ℝ) → ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x ∈ Set.Icc η (1 - η),
      |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x| < ε

/-- Endpoint smallness of the derivative profile.  For the Dirichlet/conjugate
kernel route this is supplied by continuity plus the compatibility conditions
`df 0 = 0` and `df 1 = 0`. -/
def InitialLegDerivativeEndpointSmall (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ η > 0, η < (1 / 2 : ℝ) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ η ∨ 1 - η ≤ x → |df x| < ε

/-- Endpoint-layer vanishing of the conjugate-kernel operator.  This isolates
the real boundary-layer kernel estimate from the easy endpoint compatibility
of the derivative profile. -/
def InitialLegConjugateEndpointOperatorVanish (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ η > 0, η < (1 / 2 : ℝ) ∧ ∃ δ > 0,
    ∀ t, 0 < t → t < δ → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      x ≤ η ∨ 1 - η ≤ x →
        |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)| < ε

/-- Endpoint-layer version of `InitialLegConjugateDerivativeApprox`. -/
def InitialLegConjugateDerivativeEndpointApprox (df : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ η > 0, η < (1 / 2 : ℝ) ∧ ∃ δ > 0,
    ∀ t, 0 < t → t < δ → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      x ≤ η ∨ 1 - η ≤ x →
        |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x| < ε

/-- A filter-form uniform conjugate/Dirichlet approximate identity immediately
supplies the epsilon-delta hypothesis consumed by the C1 initial-leg reducer. -/
theorem initialLegConjugateDerivativeApprox_of_tendstoUniformlyOn
    {df : ℝ → ℝ}
    (hlim : TendstoUniformlyOn
      (fun t x : ℝ =>
        -(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y))
      df (𝓝[>] (0 : ℝ)) (Set.Icc (0 : ℝ) 1)) :
    InitialLegConjugateDerivativeApprox df := by
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hlim
  have hev := hlim ε hε
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  rcases hev with ⟨δ, hδpos, hδsub⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  let I : ℝ := ∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y
  have hdist := hδsub ⟨ht, htδ⟩ x hx
  change |(-I) - df x| < ε
  have hrewrite : |(-I) - df x| = |df x + I| := by
    have harg : (-I) - df x = -(df x + I) := by ring
    rw [harg, abs_neg]
  rw [hrewrite]
  simpa [I, Real.dist_eq, add_comm, add_left_comm, add_assoc] using hdist

/-- Split reducer for `InitialLegConjugateDerivativeApprox`.

This theorem is algebra plus interval-integral linearity.  Positivity, mass
convergence, and tail/concentration estimates for the Dirichlet kernel remain
the true analytic obligations behind the two split controls. -/
theorem initialLegConjugateDerivativeApprox_of_splitControls
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hosc : InitialLegConjugateOscillationControl df)
    (hmass : InitialLegConjugateMassDefectControl df) :
    InitialLegConjugateDerivativeApprox df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hosc (ε / 2) hε2 with ⟨δo, hδo_pos, ho⟩
  rcases hmass (ε / 2) hε2 with ⟨δm, hδm_pos, hm⟩
  refine ⟨min δo δm, lt_min hδo_pos hδm_pos, ?_⟩
  intro t ht htδ x hx
  have hto : t < δo := lt_of_lt_of_le htδ (min_le_left _ _)
  have htm : t < δm := lt_of_lt_of_le htδ (min_le_right _ _)
  have ho' := ho t ht hto x hx
  have hm' := hm t ht htm x hx
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  let K : ℝ → ℝ := fun y => intervalNeumannConjugateKernel t x y
  have hdf_u : ContinuousOn df (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le h01] using hdf_cont
  have hK_u : ContinuousOn K (Set.uIcc (0 : ℝ) 1) := by
    simpa [K, Set.uIcc_of_le h01] using continuousOn_conjugateKernel_snd ht x
  have hosc_int : IntervalIntegrable
      (fun y : ℝ => (df y - df x) * K y) MeasureTheory.volume 0 1 :=
    ((hdf_u.sub continuousOn_const).mul hK_u).intervalIntegrable
  have hconst_int : IntervalIntegrable
      (fun y : ℝ => df x * K y) MeasureTheory.volume 0 1 :=
    (continuousOn_const.mul hK_u).intervalIntegrable
  have hsplit :
      -(∫ y in (0 : ℝ)..1, df y * K y) - df x =
        (-(∫ y in (0 : ℝ)..1, (df y - df x) * K y)) +
          df x * (-(∫ y in (0 : ℝ)..1, K y) - 1) := by
    have hfun :
        (fun y : ℝ => df y * K y) =
          fun y : ℝ => (df y - df x) * K y + df x * K y := by
      funext y
      ring
    rw [hfun]
    rw [intervalIntegral.integral_add hosc_int hconst_int]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [show
      (-(∫ y in (0 : ℝ)..1,
          df y * intervalNeumannConjugateKernel t x y) - df x) =
        (-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)) +
          df x * (-(∫ y in (0 : ℝ)..1,
            intervalNeumannConjugateKernel t x y) - 1) by
        simpa [K] using hsplit]
  exact lt_of_le_of_lt (abs_add_le _ _) (by
    calc
      |-(∫ y in (0 : ℝ)..1,
          (df y - df x) * intervalNeumannConjugateKernel t x y)| +
          |df x * (-(∫ y in (0 : ℝ)..1,
            intervalNeumannConjugateKernel t x y) - 1)|
          < ε / 2 + ε / 2 := add_lt_add ho' hm'
      _ = ε := by ring)

/-- Continuity plus zero endpoint values supply the endpoint-small compatibility
needed by the Dirichlet/conjugate-kernel route. -/
theorem initialLegDerivativeEndpointSmall_of_continuousOn_zero
    {df : ℝ → ℝ}
    (hdf_cont : ContinuousOn df (Set.Icc (0 : ℝ) 1))
    (hdf_zero : df 0 = 0) (hdf_one : df 1 = 0) :
    InitialLegDerivativeEndpointSmall df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hcont0 := Metric.continuousWithinAt_iff.mp
    (hdf_cont.continuousWithinAt (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  have hcont1 := Metric.continuousWithinAt_iff.mp
    (hdf_cont.continuousWithinAt (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  rcases hcont0 (ε / 2) hε2 with ⟨η0, hη0_pos, hη0⟩
  rcases hcont1 (ε / 2) hε2 with ⟨η1, hη1_pos, hη1⟩
  let η : ℝ := min (min (η0 / 2) (η1 / 2)) (1 / 4)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hη_le_η0half : η ≤ η0 / 2 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hη_le_η1half : η ≤ η1 / 2 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hη_lt_η0 : η < η0 := by linarith
  have hη_lt_η1 : η < η1 := by linarith
  have hη_lt_half : η < (1 / 2 : ℝ) := by
    have hη_le_quarter : η ≤ (1 / 4 : ℝ) := by
      dsimp [η]
      exact min_le_right _ _
    linarith
  refine ⟨η, hη_pos, hη_lt_half, ?_⟩
  intro x hx hxend
  rcases hxend with hxleft | hxright
  · have hx_lt_η0 : x < η0 := lt_of_le_of_lt hxleft hη_lt_η0
    have hdist : dist x (0 : ℝ) < η0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
      exact hx_lt_η0
    have hval := hη0 hx hdist
    exact lt_trans (by simpa [Real.dist_eq, hdf_zero] using hval) (by linarith)
  · have hx_dist : dist x (1 : ℝ) < η1 := by
      rw [Real.dist_eq]
      have hxsub_nonpos : x - 1 ≤ 0 := by linarith [hx.2]
      rw [abs_of_nonpos hxsub_nonpos]
      have hnear : 1 - x ≤ η := by linarith
      linarith
    have hval := hη1 hx hx_dist
    exact lt_trans (by simpa [Real.dist_eq, hdf_one] using hval) (by linarith)

/-- Endpoint-layer operator vanishing plus endpoint-small derivative data give
the endpoint-layer approximate identity. -/
theorem initialLegConjugateDerivativeEndpointApprox_of_operatorVanish_endpointSmall
    {df : ℝ → ℝ}
    (hop : InitialLegConjugateEndpointOperatorVanish df)
    (hsmall : InitialLegDerivativeEndpointSmall df) :
    InitialLegConjugateDerivativeEndpointApprox df := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hop (ε / 2) hε2 with ⟨ηop, hηop_pos, hηop_lt, δ, hδ_pos, hopη⟩
  rcases hsmall (ε / 2) hε2 with ⟨ηs, hηs_pos, hηs_lt, hsη⟩
  let η : ℝ := min ηop ηs
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hηop_pos hηs_pos
  have hη_lt : η < (1 / 2 : ℝ) := by
    have hle : η ≤ ηop := by dsimp [η]; exact min_le_left _ _
    exact lt_of_le_of_lt hle hηop_lt
  refine ⟨η, hη_pos, hη_lt, δ, hδ_pos, ?_⟩
  intro t ht htδ x hx hxend
  have hxend_op : x ≤ ηop ∨ 1 - ηop ≤ x := by
    rcases hxend with hxleft | hxright
    · exact Or.inl (le_trans hxleft (by dsimp [η]; exact min_le_left _ _))
    · exact Or.inr (by
        have hle : η ≤ ηop := by dsimp [η]; exact min_le_left _ _
        linarith)
  have hxend_s : x ≤ ηs ∨ 1 - ηs ≤ x := by
    rcases hxend with hxleft | hxright
    · exact Or.inl (le_trans hxleft (by dsimp [η]; exact min_le_right _ _))
    · exact Or.inr (by
        have hle : η ≤ ηs := by dsimp [η]; exact min_le_right _ _
        linarith)
  have hop_bound := hopη t ht htδ x hx hxend_op
  have hs_bound := hsη x hx hxend_s
  have htri :
      |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x|
        ≤ |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)| +
            |df x| := by
    exact abs_sub _ _
  calc
    |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) - df x|
        ≤ |-(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y)| +
            |df x| := htri
    _ < ε / 2 + ε / 2 := add_lt_add hop_bound hs_bound
    _ = ε := by ring

/-- Patching reducer: interior-strip convergence plus endpoint-layer convergence
prove the closed-interval conjugate-kernel approximate identity. -/
theorem initialLegConjugateDerivativeApprox_of_interior_endpoint
    {df : ℝ → ℝ}
    (hinterior : InitialLegConjugateDerivativeInteriorApprox df)
    (hendpoint : InitialLegConjugateDerivativeEndpointApprox df) :
    InitialLegConjugateDerivativeApprox df := by
  intro ε hε
  rcases hendpoint ε hε with ⟨η, hη_pos, hη_lt, δe, hδe_pos, he⟩
  rcases hinterior η hη_pos hη_lt ε hε with ⟨δi, hδi_pos, hi⟩
  let δ : ℝ := min δe δi
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδe_pos hδi_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht htδ x hx
  have htδe : t < δe := lt_of_lt_of_le htδ (by dsimp [δ]; exact min_le_left _ _)
  have htδi : t < δi := lt_of_lt_of_le htδ (by dsimp [δ]; exact min_le_right _ _)
  by_cases hxleft : x ≤ η
  · exact he t ht htδe x hx (Or.inl hxleft)
  · by_cases hxright : 1 - η ≤ x
    · exact he t ht htδe x hx (Or.inr hxright)
    · have hxint : x ∈ Set.Icc η (1 - η) := by
        exact ⟨le_of_lt (lt_of_not_ge hxleft), le_of_lt (lt_of_not_ge hxright)⟩
      exact hi t ht htδi x hxint

/-- If the derivative field commutes with the homogeneous semigroup leg and the
candidate derivative profile has value approximate identity, then the
homogeneous C1 initial approach follows. -/
theorem initialLegC1Approx_of_valueApprox_of_commute
    {f df : ℝ → ℝ}
    (happrox : InitialLegDerivativeValueApprox df)
    (hcomm : InitialLegDerivativeCommutes f df) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  simpa [hcomm (t := t) ht x hx] using hδ t ht htδ x hx

/-- The public source-IBP identity reduces homogeneous C1 initial approach to
the conjugate-kernel approximate identity for the derivative profile. -/
theorem initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    {f df : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf)
    (hf_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (df y) y)
    (hdf_int : IntervalIntegrable df MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox df) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - df x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  have hderiv :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x =
        -(∫ y in (0 : ℝ)..1, df y * intervalNeumannConjugateKernel t x y) :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
      (t := t) ht (Q := f) (Q' := df) hf_meas hf_bound hf_deriv hdf_int x
  rw [hderiv]
  exact hδ t ht htδ x hx

/-- Source-IBP reducer through a global C1 representative `Q` that agrees with
the desired source `f` on `[0,1]`.  This is the safer form for zero-extended
interval data, whose raw lift need not be globally differentiable at the
endpoints. -/
theorem initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    {f Q dQ : ℝ → ℝ}
    (hfQ : ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (dQ y) y)
    (hdQ_int : IntervalIntegrable dQ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox dQ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x - dQ x| < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht htδ x hx
  have hfun :
      (fun z : ℝ => intervalFullSemigroupOperator t f z) =
        fun z : ℝ => intervalFullSemigroupOperator t Q z := by
    funext z
    exact intervalFullSemigroupOperator_congr_on_Icc hfQ t z
  rw [hfun]
  have hderiv :
      deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x =
        -(∫ y in (0 : ℝ)..1, dQ y * intervalNeumannConjugateKernel t x y) :=
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
      (t := t) ht (Q := Q) (Q' := dQ) hQ_meas hQ_bound hQ_deriv hdQ_int x
  rw [hderiv]
  exact hδ t ht htδ x hx

/-- The existing uniform value approximate identity supplies
`InitialLegDerivativeValueApprox` for a globally continuous derivative
representative. -/
theorem derivativeValueApprox_of_continuous
    (df : ℝ → ℝ) (hdf : Continuous df) :
    InitialLegDerivativeValueApprox df := by
  intro ε hε
  have htend :=
    ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn df hdf
  rw [Metric.tendstoUniformlyOn_iff] at htend
  have hev := htend ε hε
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  rcases hev with ⟨δ, hδmem, hδsub⟩
  refine ⟨δ, hδmem, ?_⟩
  intro t ht htδ x hx
  have hdist := hδsub ⟨ht, htδ⟩ x hx
  simpa [Real.dist_eq, abs_sub_comm] using hdist

/-- Domain-facing conditional homogeneous C1 initial approach.  This is the
metric wrapper needed by the zero-start derivative route once the genuine
commutation/IBP theorem is supplied. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_global_deriv_continuous_of_commute
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀x_cont : Continuous (fun x : ℝ => deriv (intervalDomainLift u₀) x))
    (hcomm : InitialLegDerivativeCommutes
      (intervalDomainLift u₀)
      (fun x : ℝ => deriv (intervalDomainLift u₀) x)) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          deriv (intervalDomainLift u₀) x| < ε :=
  initialLegC1Approx_of_valueApprox_of_commute
    (derivativeValueApprox_of_continuous
      (fun x : ℝ => deriv (intervalDomainLift u₀) x) hu₀x_cont)
    hcomm

/-- Domain-facing source-IBP reducer for the homogeneous C1 initial approach.
The derivative profile `du₀` is explicit, and the only convergence hypothesis is
the conjugate-kernel approximate identity for `du₀`. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_conjugateApprox
    {u₀ : intervalDomainPoint → ℝ} {du₀ : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ Cu₀)
    (hu₀_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (intervalDomainLift u₀) (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox du₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_sourceIBP
    hu₀_meas hu₀_bound hu₀_deriv hdu₀_int happrox

/-- Domain-facing representative form for interval initial data.  The global
representative `Q` supplies the differentiability required by source IBP, while
the semigroup still acts on the original zero-extended interval source. -/
theorem intervalFullSemigroup_initialLegC1Approx_of_Icc_repr_conjugateApprox
    {u₀ : intervalDomainPoint → ℝ} {Q du₀ : ℝ → ℝ}
    (hu₀Q : ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift u₀ y = Q y)
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (du₀ y) y)
    (hdu₀_int : IntervalIntegrable du₀ MeasureTheory.volume 0 1)
    (happrox : InitialLegConjugateDerivativeApprox du₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        |deriv (fun z : ℝ =>
            intervalFullSemigroupOperator t (intervalDomainLift u₀) z) x -
          du₀ x| < ε :=
  initialLegC1Approx_of_conjugateApprox_of_Icc_repr
    hu₀Q hQ_meas hQ_bound hQ_deriv hdu₀_int happrox

end

end ShenWork.IntervalSemigroupC1ApproxIdentity
