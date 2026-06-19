# Paper-1 wave — final honest ceiling (2026-06-19, after the Schauder elimination)

## What is DONE (axiom-clean, build-verified), all in our own tree — no Mathlib gap
- The Schauder fixed-point principle + the WaveTrap fixed point: PROVED from our own brouwer_fixedPoint
  (n-dim Sperner) + ε-net + the antitone-majorant retraction + continuous-image (c709329). The wave headline
  `wholeLine_travelingWave_exists_consolidated` carries NO Schauder hypothesis (verified: zero schauder residual).
- The heat-semigroup generator identity (Gaussian solves heat eq + Leibniz under convolution).
- The 1D weak→classical elliptic regularity keystone (reusable).
- The weak-stationary limit + the 14 residual fields' discharges (profile regularity via weak+elliptic,
  monotonicity, continuity, uniform tail, flat-left, left-tail via T10, etc.).
- Const-barrier trapping UNCONDITIONAL; Paper-2 χ₀=0 UNCONDITIONAL.

## The IRREDUCIBLE remaining frontier — the concrete aux-flow (moving-frame) parabolic existence
The wave headline reduces to `WholeLineAuxiliaryGlobalFamilyData` (Haux) + its parabolic-regularity inputs.
Haux's three analytic fields are NOT wirings of existing lemmas — the banked Contraction/Global theorems CONSUME
them as inputs:
- `rate`  : AuxiliaryMildMapRateEstimates — the moving-frame mild map's L∞/√T-gradient contraction constants
  A,B. (Related banked: movingFrameHeatGradOp bounds in WholeLineParabolicEquicontinuity — a START, not the
  full rate estimate.)
- `realize`: AuxiliaryMildMapBanachRealizationData — the actual Banach fixed point of the moving-frame mild map.
- `restart`: AuxiliaryUniformRestartGluingFromLocalBanach — the continuation/gluing to global time.
These are the genuine moving-frame parabolic existence/regularity — the SAME kind of analytic content Paper-2's
framework built for the BOUNDED domain (IntervalDomainExistence etc.), now needed on ℝ in the moving frame.
This is real PDE analysis (substantial), satisfiable for a real aux-flow — the FAITHFUL conditional content.
This is the honest ceiling: the wave existence reduces to the concrete moving-frame parabolic existence, with
NO Mathlib gap and NO Schauder hypothesis. Every "gap" mis-claimed earlier (Brouwer, heat theory, Schauder) is
now proved in our own tree.
