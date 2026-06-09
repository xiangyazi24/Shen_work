# Worker Status

## 2026-06-09 — adapter sorry tasks

### Task 1: constExtend_continuous
- **Status**: DONE ✓
- **File**: ShenWork/PDE/IntervalDomainContinuousExtension.lean:61
- **Commit**: e563d75
- **Verification**: `lake env lean` EXIT 0 (local, verified)
- **Approach**: Bridge lemma `constExtend = IccExtend zero_le_one f` via funext + split_ifs + Subtype.ext with min/max simp, then `Continuous.Icc_extend'` from Mathlib. Also fixed: definition used nonexistent `le_of_not_le` (→ dite form); `constExtend_eq_lift_on_Icc` used `le_or_lt` (→ by_cases); added local TopologicalSpace instance (olean stale).

### Task 2: cosineCoeffs_constExtend_eq_lift
- **Status**: DONE ✓ (pending remote verification)
- **File**: ShenWork/PDE/IntervalDomainContinuousExtension.lean:78
- **Commit**: 8402f85
- **Verification**: NEEDS REMOTE BUILD (IntervalNeumannFullKernel.olean missing locally)
- **Approach**: Unfold cosineCoeffs → unitIntervalNeumannCosineCoeff → unitIntervalCosineRawCoeff (interval integral ∫₀¹), apply `intervalIntegral.integral_congr` + `constExtend_eq_lift_on_Icc`. Pattern copied from PROVED `ConstExtendAdapter.cosineCoeffs_constExtend_eq_lift`.

### Task 3: semigroupOperator_constExtend_eq_lift
- **Status**: DONE ✓ (pending remote verification)
- **File**: ShenWork/PDE/IntervalDomainContinuousExtension.lean:90
- **Commit**: 8402f85
- **Verification**: NEEDS REMOTE BUILD (IntervalNeumannFullKernel.olean missing locally)
- **Approach**: Unfold intervalFullSemigroupOperator + intervalMeasure + intervalSet to ∫ K*f ∂(volume.restrict Icc), apply `integral_congr_ae` + `ae_restrict_mem measurableSet_Icc` + `constExtend_eq_lift_on_Icc`.

### Task 4: hLc (logistic source subtype continuity)
- **Status**: DONE ✓ (pending remote verification)
- **File**: ShenWork/Paper2/IntervalDomainThm11ChiZeroCoreProvider.lean:222
- **Commit**: 2a3c7b6
- **Verification**: NEEDS REMOTE BUILD (Paper2 olean cache missing locally)
- **Approach**: `D.hcont s hs (hsT.trans htT.le)` gives Continuous (D.u s); unfold intervalLogisticSource; exact hcu.mul (continuous_const.sub (continuous_const.mul (hcu.rpow_const (fun _ => Or.inr p.hα.le)))). Pattern verified in IntervalDuhamelIntegrability.lean:329-333.

## Build note
Local olean cache is very sparse (only IntervalDomain, HeatSemigroup, BoundedDomainData, Defs). All Tasks except Task 1 need remote `lake build` on uisai1 for full verification.
