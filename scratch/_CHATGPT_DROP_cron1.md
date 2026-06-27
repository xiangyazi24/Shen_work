# Q1391 (cron1) — `cron-shen`

Repository: `xiangyazi24/Shen_work`

Branch updated: `chatgpt-scratch`

Target file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Scope / method

The user prompt body was only:

```text
Q1391 (cron1): cron-shen
```

There is still no specific Lean theorem, error message, file line, or requested proof in the prompt.  I therefore interpret this as another cron-shen status/dispatch drop, continuing Q1378/Q1379/Q1381, and I refresh the report using the latest repository-visible status artifacts.

Delivery constraints respected:

```text
GitHub connector only.
No Python / code-interpreter.
No /mnt/data writes.
No sandbox link.
No Lean/source-code modifications.
No local or remote lake build run by this drop.
```

Files/status artifacts inspected for this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
THREE_PAPER_BOARD.md
CHINEG_CHECKLIST.md
RUN_LOG.md
ShenWork/Paper2/IntervalChiNegDirectSupersolution.lean
```

Important source ordering:

```text
CHINEG_CHECKLIST.md is now the most precise live tracker for the χ₀<0 lane.
THREE_PAPER_BOARD.md remains the cross-paper board and is still best for P1/P3 context.
IntervalChiNegDirectSupersolution.lean confirms that the direct supersolution route exists in code.
```

## Branch status at drop time

GitHub compare result for `main...chatgpt-scratch` at this drop:

```text
status: diverged
ahead_by: 280
behind_by: 387
merge_base: 954c43ef4e696e78e5724f53b7ddab7c89be140a
main/base commit: 8432432508519d1720c8b51fa566d72466eb1708
```

So `chatgpt-scratch` remains an active scratch/status branch diverged from `main`.  This drop only overwrites this scratch markdown file.

## High-level update since Q1381

Q1381 said the next χ₀<0 target was the direct gW-inflated H^σ supersolution route.  That is now **superseded** by the checklist/code state:

```text
hEhatH / direct supersolution route is DISCHARGED.
crux B / source-generic semigroup joint continuity is DONE.
hmean0 is closing / in flight.
After hmean0, χ₀<0 is conditional on only crux A.
```

The new main live χ₀<0 frontier is:

```text
CRUX A:
  the uniform-in-time H^σ flux envelope g/gl.
```

This is the circularity where the box-extend induction needs `genv` per restart, but `genv_of_trajectoryEnvelope_uncond` wants the global coordinatewise envelope rather than a partial `BoundUpTo r`.  The checklist describes the needed fix as a uniform flux bound **without** the global `genv`, i.e. the uniform a-priori estimate.

## χ₀<0 lane — current precise status

Target capstone:

```text
meanReach_H1_conjugate
```

and downstream:

```text
ChiNegDatumUniformConstruction p
```

### Discharged / banked according to `CHINEG_CHECKLIST.md`

The checklist records the following as discharged:

```text
hEhatH   — supersolution H^σ via direct Duhamel-deflation route, memHSigma_deflate (aa8fe53)
hWsum    — reflCircle ℓ¹ of W=lift(u)·denom via reflCircle_mul_fourier_summable (820b383)
hvnn     — resolver positivity via carrySeam_hvnn / cone / resolverValue_nonneg (820b383)
hmean    — k=0 mean bound
hdecomp_pos τ=0 — decomp_tau0
```

The direct supersolution file exists and encodes the intended route:

```lean
-- File: ShenWork/Paper2/IntervalChiNegDirectSupersolution.lean

theorem memHSigma_deflate {σ : ℝ} (hσ : 0 ≤ σ) {M : ℕ → ℝ}
    (hM : MemHSigma σ M) :
    MemHSigma σ (fun k => M k / (1 + lam k) ^ (σ / 2)) := by
  ...

def chemDuhamel_direct ... :
    TrajectoryHSigmaEnvelope (σ + α) t
      (fun s k => duhamelEnergyCoeff 1 (fun k τ => sineCoeffs (Q τ) k) s k) :=
  trajectoryEnvelope_of_sourceEnvelope ...

def trajEnvelope_chiNeg_direct ... :
    TrajectoryHSigmaEnvelope (σ + α) t (fun τ => cosineCoeffs (u τ)) :=
  trajLadder_step_meanFixed ...
```

The file also contains `#print axioms` commands for these three declarations.  I did not run Lean in this drop, so I am only reporting what is in the repository-visible source and checklist.

### Direct supersolution route — current interpretation

The direct route bypasses the old bare-sineEnv artifact:

```text
Wrong/obsolete interface:
  force M under bare sineEnv Estar = √λ·Estar/(1+λ), causing a fake +1 derivative demand.

Correct/direct interface:
  the Duhamel kernel already carries √λ, and hSigma_mode_duhamel_bound gives direct deflation.
```

Core message:

```text
If M ∈ H^σ, the chemotaxis Duhamel contribution is controlled by
  C' * M_k / (1 + λ_k)^(σ/2),
which stays in H^σ.
```

So Q1381's “Priority 1 direct supersolution” should now be considered done/banked unless a later build contradicts it.

### Current χ₀<0 residual surface

The checklist has an older open-list section, but its latest end-to-end section supersedes it.  The current actionable residuals are:

```text
hmean0 — wiring/in flight:
  cosine→mean bridge is built; datum bound |u₀ x|≤M is closing via Core.hbase_ball and t→0⁺ strong-continuity.
  The checklist names a262631a as in flight.  Do not assume complete until committed/verified.

CRUX A — the genuine deep PDE frontier:
  uniform-in-time H^σ flux envelope g/gl.
  The box-extend induction needs genv per restart, but genv wants a global coordinatewise envelope.
  The circularity must be broken by a uniform flux bound without the global genv.
```

`crux B` is now listed as done:

```text
valueOp_src_jointCont + logisticLeg_continuous_full (092bee5), axiom-clean.
```

### Best next χ₀<0 dispatch

Use this order:

```text
1. Check/finish hmean0.
   - If a262631a or successor is committed and verified, mark hmean0 closed.
   - If not, finish the datum bound |u₀ x|≤M from Core.hbase_ball + t→0⁺ strong-continuity.

2. Attack CRUX A directly.
   - Target: uniform-in-time H^σ flux envelope g/gl.
   - Avoid: restarting the direct supersolution route; it is already discharged.
   - Avoid: BCF/trajBanach closed-box continuity at τ=0; checklist says that approach is unsatisfiable/vacuous because the semigroup convention jumps at τ=0.
   - Use: direct domination / TrajectoryHSigmaEnvelope structure; no BCF self-map at τ=0.

3. After CRUX A, wire the final chiNeg H¹ envelope into ChiNegDatumUniformConstruction.
```

Concrete next-worker prompt for χ₀<0:

```text
Read CHINEG_CHECKLIST.md latest entries.  Do not redo hEhatH/direct supersolution, hvnn, hWsum, or crux B; they are listed as discharged.  First determine whether hmean0 from a262631a or a successor is committed/verified.  If not, finish hmean0 by extracting |u₀ x|≤M from Core.hbase_ball plus the t→0⁺ strong-continuity limit.  Then target CRUX A: produce the uniform-in-time H^σ flux envelope g/gl without assuming the global coordinatewise envelope needed by genv.  The box-extend induction needs a restart-local uniform flux bound; do not use the vacuous BCF/trajBanach τ=0 route.  Acceptance: relevant build green, #print axioms clean, and chiNeg_H1/meanReach_H1_conjugate carries only the faithful initial/parameter hypotheses plus no hidden conclusion-equivalent envelope assumption.
```

## P1 lane — current status from `THREE_PAPER_BOARD.md`

The latest cross-paper board still gives the P1 endpoint from Q1381:

```text
P1 admissible_closure hin floor DISCHARGED (684e811, verified 8319 @HEAD).
P1 now carries ONLY the per-step RotheFloorOrbitDataResidual for the PRODUCED W.
```

Meaning:

```text
- admissible_closure is built;
- RotheStepInput/hin was discharged through the residual provider;
- the remaining per-step frontier is not another wrapper;
- the closed solve gives the truncated fixed point, while the residual needs the untruncated source R=crossSource plus whole-line flux IBP/source data.
```

Current P1 next target:

```text
RotheFloorOrbitDataResidual for the produced W.
```

Concrete P1 worker prompt:

```text
Read the latest THREE_PAPER_BOARD.md P1 entries.  Do not rebuild admissible_closure or RotheStepInput/hin; they are listed as discharged.  Target RotheFloorOrbitDataResidual for the produced W.  Supply the untruncated source R=crossSource and whole-line flux IBP / endpoint-source data required by the orbit residual.  Do not add another residual wrapper and do not use the false pointwise RotheChemoMonotoneResidual route.  Acceptance: construction_neg consumes the produced residual through the live producer chain, relevant build green, #print axioms clean.
```

## P3 lane

No newer P3-specific update appears in the inspected latest status artifacts.  The current practical state remains:

```text
P3 T2.2 cascades from χ₀<0.
```

Do not prioritize broad P3 unless explicitly requested.  A narrow P3 task would be reasonable only if it asks for a specific spectral/fractional-power lemma or an axiom audit of a known target.

## Updated priority queue after Q1391

```text
Priority 1 — χ₀<0 hmean0 sanity/closure:
  Verify whether a262631a or successor landed; if not, finish the datum-bound extraction.

Priority 2 — χ₀<0 CRUX A:
  Uniform-in-time H^σ flux envelope g/gl, avoiding the global-genv circularity.

Priority 3 — P1 construction_neg:
  RotheFloorOrbitDataResidual for the produced W: untruncated source + whole-line flux IBP/source endpoint data.

Priority 4 — final χ₀<0 wiring:
  After crux A, wire chiNeg_H1 / meanReach_H1_conjugate into ChiNegDatumUniformConstruction.

Priority 5 — P3:
  Keep broad T2.2 behind χ₀<0 unless explicitly requested.
```

## What should be considered stale now

```text
Stale: Q1381 priority to build IntervalChiNegDirectSupersolution.lean from scratch.
Current: the file exists and hEhatH is listed discharged.

Stale: broad Hpersist label as the only χ₀<0 issue.
Current: the live residual is hmean0-in-flight plus CRUX A uniform-in-time H^σ flux envelope.

Stale: BCF/trajBanach closed-box continuity route at τ=0.
Current: checklist says it is vacuous/unsatisfiable under the repo's τ=0 semigroup convention; direct TrajectoryHSigmaEnvelope domination is the live route.

Stale: P1 hin/RotheStepInput as the current bottom.
Current: hin discharged; P1 bottom is RotheFloorOrbitDataResidual for produced W.
```

## Final status sentence

The Q1391 cron-shen state is:

```text
The χ₀<0 direct supersolution route has landed; crux B is done; hmean0 is in flight; after hmean0 the only listed χ₀<0 core is CRUX A, the uniform-in-time H^σ flux envelope g/gl.  P1 has discharged admissible_closure/hin and now bottoms at RotheFloorOrbitDataResidual for the produced W.  Broad wrapper work and the old BCF τ=0 route should stop.
```

## Delivery note

This commit only updates `scratch/_CHATGPT_DROP_cron1.md` on `chatgpt-scratch`.  It does not modify Lean source and does not claim any new build result.