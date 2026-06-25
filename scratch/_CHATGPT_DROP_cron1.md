# Q480 / cron1: direct `IntervalWeakH2Neumann` construction avoiding zero-extension endpoint tendsto

## Executive verdict

I found **one genuinely useful direct constructor** that does **not** require endpoint `Tendsto` hypotheses on the target zero-extension function:

```lean
IntervalWeakH2Neumann.congr_on_Icc
```

in `ShenWork/Paper2/IntervalDomainLogisticWeakH2Adapter.lean`.

It is a record-literal transfer theorem: if `hf : IntervalWeakH2Neumann f` and `f = g` on `[0,1]`, then it builds `IntervalWeakH2Neumann g` with the **same** `secondDeriv`, `second_intervalIntegrable`, and `weak_cosine_laplacian`, because the structure only sees `g` through the integral `∫₀¹ cos · g`.  This is exactly the zero-extension bypass pattern.

However, I did **not** find an existing direct constructor specialized to

```lean
IntervalWeakH2Neumann (chemDivLift p u v)
```

or to a generic smooth `φ'`/`φ'''` pair.  The existing chem-div source tools either:

1. still call `intervalWeakH2Neumann_of_contDiffOn` and require endpoint data, or
2. carry `IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)` as a residual field, or
3. prove coefficient decay from an already-built `IntervalWeakH2Neumann` certificate.

So the shortest viable route for `chemDivLift p u v` is likely:

```text
Build an IntervalWeakH2Neumann certificate for a smooth representative F
that agrees with chemDivLift p u v on [0,1], then transfer it by
IntervalWeakH2Neumann.congr_on_Icc.
```

This avoids proving endpoint `Tendsto` for the zero-extension itself.  It does **not** avoid proving the weak cosine Laplacian identity for the smooth representative.  That identity still has real boundary terms; endpoint values are not magically erased by measure-zero arguments.

---

## 1. Definition of `IntervalWeakH2Neumann`

`ShenWork/PDE/IntervalMildSourceDecayHelper.lean` defines the structure:

```lean
/-- A lightweight weak `H²_N` certificate on `[0,1]`.

The field `weak_cosine_laplacian` is the Neumann cosine weak-IBP identity.  The
`second_abs_integral_bound` field is the `L¹` control implied by an `L²` weak
second derivative on the finite interval. -/
structure IntervalWeakH2Neumann (f : ℝ → ℝ) where
  secondDeriv : ℝ → ℝ
  second_intervalIntegrable : IntervalIntegrable secondDeriv volume (0 : ℝ) 1
  second_abs_integral_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∫ x in (0 : ℝ)..1, |secondDeriv x| ≤ B
  weak_cosine_laplacian : ∀ k : ℕ,
    (∫ x in (0 : ℝ)..1,
        Real.cos ((k : ℝ) * Real.pi * x) * secondDeriv x) =
      -((k : ℝ) * Real.pi) ^ 2 *
        ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x
```

The standard constructor is:

```lean
noncomputable def intervalWeakH2Neumann_of_contDiffOn
    {g : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv g) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv g) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv g 0 = 0) (hbc1 : deriv g 1 = 0) :
    IntervalWeakH2Neumann g where
  secondDeriv := deriv (deriv g)
  second_intervalIntegrable :=
    intervalIntegrable_deriv_deriv_of_contDiffOn_two hgC2
  second_abs_integral_bound := by
    refine ⟨∫ x in (0 : ℝ)..1, |deriv (deriv g) x|, ?_, le_rfl⟩
    exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun x _hx => abs_nonneg _)
  weak_cosine_laplacian := by
    intro k
    exact intervalCosineLaplacianCoeff_eq_of_contDiffOn k hgC2 htend0 htend1 hbc0 hbc1
```

So the default path is exactly the endpoint-tendsto path you want to avoid for zero-extension functions.

---

## 2. Direct constructor found: `IntervalWeakH2Neumann.congr_on_Icc`

The key direct constructor is in `ShenWork/Paper2/IntervalDomainLogisticWeakH2Adapter.lean`:

```lean
/-- **Weak-H²/Neumann certificate transfers across `[0,1]`-agreement.**  The
certificate uses its function `f` only through the `∫₀¹ cos·f` integral, so two
functions equal on `[0,1]` share it (with the SAME `secondDeriv`). -/
def _root_.ShenWork.PDE.IntervalMildSourceDecayHelper.IntervalWeakH2Neumann.congr_on_Icc
    {f g : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) :
    IntervalWeakH2Neumann g where
  secondDeriv := hf.secondDeriv
  second_intervalIntegrable := hf.second_intervalIntegrable
  second_abs_integral_bound := hf.second_abs_integral_bound
  weak_cosine_laplacian := fun k => by
    have hint : (∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * g x)
        = ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * Real.pi * x) * f x := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [hfg x hx]
    rw [hint]; exact hf.weak_cosine_laplacian k
```

This is directly relevant to your situation.  It says: do **not** try to prove endpoint tendsto for the zero-extension target.  Instead, build the weak-H² certificate for a nicer representative, then transfer across equality on `[0,1]`.

For `chemDivLift p u v`, the candidate shape is:

```lean
let U := intervalDomainLift u
let V := intervalDomainLift v
let φ := chemFluxFun p.β U V
let F := deriv φ

-- 1. prove hf : IntervalWeakH2Neumann F
-- 2. prove hEq : ∀ x ∈ Icc 0 1, F x = chemDivLift p u v x
-- 3. exact hf.congr_on_Icc hEq
```

The equality in step 2 is the same bridge from Q463.

---

## 3. Representation-based direct constructors also exist, but only for power/logistic source families

`IntervalDomainLogisticWeakH2Adapter.lean` uses `congr_on_Icc` to avoid global C²/tendsto demands on zero-extensions.  The logistic source constructor is:

```lean
/-- **Logistic-source weak-H²/Neumann certificate from the cosine representation.**

For a positive profile `w` whose lift agrees on `[0,1]` with an eigenvalue-summable
cosine series, the logistic source `logisticSourceFun a b α (lift w)` has the
weak-H²/Neumann certificate — built from the genuinely-`C²` cosine series, with NO
global-`C²` hypothesis on the (zero-extended) lift. -/
def logisticSource_intervalWeakH2Neumann_of_eigenvalue_summable
    {a b α : ℝ} {bc : ℕ → ℝ}
    (hbsum : Summable (fun n => unitIntervalCosineEigenvalue n * |bc n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, bc n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    IntervalWeakH2Neumann (logisticSourceFun a b α (intervalDomainLift w)) := by
  have hC2 : ContDiff ℝ 2 (fun x => ∑' n, bc n * cosineMode n x) :=
    ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two hbsum
  ...
  have hwH2 : IntervalWeakH2Neumann
      (logisticSourceFun a b α (fun x => ∑' n, bc n * cosineMode n x)) :=
    logisticSourceFun_intervalWeakH2Neumann hC2 hpos_cs hd0 hd1
  refine hwH2.congr_on_Icc (fun x hx => ?_)
  simp only [logisticSourceFun]
  rw [hagree hx]
```

This is not for `chemDivLift`, but it is the exact architectural pattern you want: build a certificate for a smooth cosine representative, then transfer by `[0,1]` equality.

The same file also points to the power-source analogue:

```lean
ShenWork.PDE.IntervalMildSourceDecayHelper.intervalWeakH2Neumann_of_eigenvalue_summable
```

but that power-source constructor still ultimately uses `intervalWeakH2Neumann_of_contDiffOn` after proving endpoint data for the power source.

---

## 4. Existing `intervalWeakH2Neumann_of_eigenvalue_summable` still uses the endpoint constructor internally

In `IntervalMildSourceDecayHelper.lean`, the power-source constructor is not a pure direct record literal.  It proves endpoint data and then calls the standard constructor:

```lean
noncomputable def intervalWeakH2Neumann_of_eigenvalue_summable
    {ν γ : ℝ} (hν : 0 < ν) (hγ : 0 < γ)
    {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    {w : intervalDomainPoint → ℝ}
    (hagree : Set.EqOn (intervalDomainLift w)
        (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift w x) :
    IntervalWeakH2Neumann (fun x : ℝ => ν * intervalDomainLift w x ^ γ) := by
  ...
  exact intervalWeakH2Neumann_of_contDiffOn hC2g htend0 htend1 hbc0 hbc1
```

So it is zero-extension-aware, but not a direct replacement for your request.

---

## 5. Existing chem-div constructors still depend on C²/Neumann or residual data

For chem-div, the currently landed constructor is only conditional:

```lean
/-- **Per-slice weak-`H²ₙ` certificate for the chem-div source.**

From the source slice being `C²` on `[0,1]` with homogeneous Neumann endpoint
data, the committed `intervalWeakH2Neumann_of_contDiffOn` packager yields the
weak `H²_N` certificate whose weak second derivative is `deriv (deriv f)`. -/
def chemDivSource_weakH2_of_spatialC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hC2 : ContDiffOn ℝ 2 (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    (ht0 : Tendsto (deriv (coupledChemDivSourceLift p u s))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (ht1 : Tendsto (deriv (coupledChemDivSourceLift p u s))
      (nhdsWithin (1 : ℝ) (Iio 1)) (nhds 0))
    (hbc0 : deriv (coupledChemDivSourceLift p u s) 0 = 0)
    (hbc1 : deriv (coupledChemDivSourceLift p u s) 1 = 0) :
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s) :=
  intervalWeakH2Neumann_of_contDiffOn hC2 ht0 ht1 hbc0 hbc1
```

And in `IntervalChemDivSpatialC2.lean`, the planned `chemDivSource_weakH2_of_uv_C4` still has the TODO/sorry comment:

```lean
noncomputable def chemDivSource_weakH2_of_uv_C4
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiffOn ℝ 4 (intervalDomainLift u) (Icc (0 : ℝ) 1))
    (hv : ContDiffOn ℝ 4 (intervalDomainLift v) (Icc (0 : ℝ) 1))
    ... :
    IntervalWeakH2Neumann (chemDivLift p u v) := by
  sorry
  -- Wires chemDivLift_contDiffOn_two + chemDivLift_neumann_bc
  -- into chemDivSource_weakH2_of_spatialC2. Blocked on the 3 sorry above.
```

So there is no existing direct chem-div weak-H² constructor in the repo.

The residual route carries the certificate as data.  `IntervalChemDivWinDischarge.lean` defines:

```lean
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  ...
  hH2 : ∀ s, 0 ≤ s → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
  ...
```

That confirms the current state: chem-div weak-H² is still an input/residual, not produced directly.

---

## 6. The proposed `φ'`/`φ'''` direct construction has a real boundary-term obligation

Suppose

```lean
φ := chemFluxFun p.β (intervalDomainLift u) (intervalDomainLift v)
f := φ'
secondDeriv := φ'''
```

Then the weak identity asks:

```lean
∫₀¹ cos(kπx) φ'''(x) dx
  = -((kπ)^2) * ∫₀¹ cos(kπx) φ'(x) dx
```

Two integrations by parts give:

```text
∫ cos φ''' = [cos · φ'']₀¹ - (kπ)^2 ∫ cos φ'
```

because the intermediate sine boundary term vanishes.  Thus the desired weak identity requires

```text
[cos(kπx) · φ''(x)]₀¹ = 0
```

for every `k`.  Equivalently, it forces endpoint conditions strong enough to make the flux second derivative vanish in the correct cosine parity sense, typically `φ''(0)=φ''(1)=0` if the identity is to hold for all modes.

So the “integrals ignore endpoints” observation helps you transfer `f` across pointwise endpoint mismatches, but it does **not** erase the boundary term in the weak Laplacian identity.  The direct record-literal construction still needs a proof of the `weak_cosine_laplacian` field, and that proof has endpoint/parity content.

This is why `congr_on_Icc` is useful but not a complete solution: it lets you avoid endpoint tendsto for the zero-extension target, but you must still build a valid weak-H² certificate for some smooth representative.

---

## 7. Recommended route for `chemDivLift p u v`

The cleanest repo-compatible design is:

```lean
-- Smooth representative:
let U : ℝ → ℝ := <global cosine representative for intervalDomainLift u on [0,1]>
let V : ℝ → ℝ := <global cosine representative for intervalDomainLift v on [0,1]>
let φ : ℝ → ℝ := chemFluxFun p.β U V
let F : ℝ → ℝ := deriv φ
let SD : ℝ → ℝ := deriv (deriv (deriv φ))
```

Then prove a new direct constructor with explicit boundary/parity assumptions:

```lean
noncomputable def intervalWeakH2Neumann_of_flux_derivative
    {φ F SD : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc (0:ℝ) 1, F x = deriv φ x)
    (hSD : ∀ x ∈ Set.Icc (0:ℝ) 1, SD x = deriv (deriv (deriv φ)) x)
    (hSD_int : IntervalIntegrable SD volume 0 1)
    (hSD_bound : ∃ B, 0 ≤ B ∧ ∫ x in (0:ℝ)..1, |SD x| ≤ B)
    (hweak : ∀ k,
      (∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * SD x)
        = -((k:ℝ) * Real.pi)^2 *
          ∫ x in (0:ℝ)..1, Real.cos ((k:ℝ) * Real.pi * x) * F x) :
    IntervalWeakH2Neumann F :=
{ secondDeriv := SD
  second_intervalIntegrable := hSD_int
  second_abs_integral_bound := hSD_bound
  weak_cosine_laplacian := hweak }
```

Then transfer:

```lean
have hF_H2 : IntervalWeakH2Neumann F := ...
have hEq : ∀ x ∈ Set.Icc (0:ℝ) 1, F x = chemDivLift p u v x := ...
exact hF_H2.congr_on_Icc hEq
```

This is the repo's existing pattern, and it avoids the false endpoint tendsto demand on the zero-extension target.

---

## Final answer

* There is **no existing direct `IntervalWeakH2Neumann (chemDivLift p u v)` constructor** that bypasses `intervalWeakH2Neumann_of_contDiffOn`.
* The key existing tool is `IntervalWeakH2Neumann.congr_on_Icc`, which transfers a weak-H² certificate across equality on `[0,1]` without endpoint tendsto for the target.
* Representation-based constructors for logistic/power sources already use this pattern; they build a certificate for a smooth cosine representative and transfer to the zero-extension/physical source.
* For chem-div, you still need to build the weak cosine Laplacian identity for a smooth representative. Integrals ignoring endpoint values are not enough: the triple-derivative IBP has a boundary term `[cos(kπx) φ''(x)]₀¹` that must vanish.
* Therefore the recommended patch is to add a new smooth-representative direct constructor, prove the boundary/parity weak identity there, and then use `IntervalWeakH2Neumann.congr_on_Icc` to transfer to `chemDivLift p u v`.
