# Q1066 / cron1 — exact Level0 proof body for SORRY 3C+3D+3F

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

The exact replacement should use the **local** bridge

```lean
coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
```

rather than the global convenience wrapper

```lean
coupledChemDivFlux_timeBridge_of_physicalJointC2
```

inside the current `IntervalConjugateLevel0BFormSourceOn.lean` block.

Reason: the current Level0 `hlocal_slab` branch has only a pointwise/local heat fact

```lean
_hu_c2_bridged : ContDiffAt ℝ 2
  (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
  (r, x)
```

and a pointwise positivity fact

```lean
hbase : 0 < 1 + intervalDomainLift
  (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) r) x
```

whereas `coupledChemDivFlux_timeBridge_of_physicalJointC2` asks for global hypotheses

```lean
hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, ContDiffAt ... (s, x)
hbase : ∀ s : ℝ, ∀ x : ℝ, 0 < 1 + intervalDomainLift ... x
```

Those global hypotheses are deliberately not available after the positive-time weakening. The proof below stays local: it reconstructs the needed positive-time heat `u` joint-C² near `(r,x)`, obtains 3C/3D from `PhysicalResolverJointC2Data`, obtains the resolver inner commute from `coupledChemical_innerCommute_of_physicalJointC2`, derives the required eventual floor from `hbase` and `hv_c2.continuousAt`, and then applies the existing Clairaut bridge.

## Required import

Add this import to `IntervalConjugateLevel0BFormSourceOn.lean` if it is not already present:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
```

`IntervalChemDivFACCommuteDischarge` imports the physical resolver producers and the flux time bridge chain.

## Required hypothesis name

The proof body below assumes that the Level0 theorem has a physical resolver datum in scope named `Hphys`:

```lean
{Bt : ℕ → ℕ → ℝ}
(Hphys : ShenWork.IntervalResolverJointC2PhysicalConcrete.PhysicalResolverJointC2Data
  p (conjugatePicardIter p u₀ 0) Bt)
```

If the actual hypothesis has a different name, rename `Hphys` in the body.

## Exact replacement body for the 3C+3D+3F sorry

This is intended to replace exactly the combined sorry immediately after the local `hbase` proof in the `intro x hx r hr` branch.

```lean
      let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
      change HasDerivAt
        (fun t : ℝ => coupledChemDivSourceLift p u t x)
        (coupledChemDivTimeDerivativeLift p u r x) r

      have hbase_u : 0 < 1 + intervalDomainLift
          (coupledChemicalConcentration p u r) x := by
        simpa [u] using hbase

      have hu_c2_rx : ContDiffAt ℝ 2
          (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (r, x) := by
        simpa [u] using _hu_c2_bridged

      -- Positive-time heat joint-C² at any nearby interior point.  This is the
      -- same bridge as `_hu_c2_bridged`, repackaged for the local-event uses
      -- needed by the spatial and time partial bridges.
      have hu_c2_at : ∀ {t y : ℝ}, 0 < t → y ∈ Ioo (0 : ℝ) 1 →
          ContDiffAt ℝ 2
            (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (t, y) := by
        intro t y ht hy
        have ht_half_pos : (0 : ℝ) < t / 2 := half_pos ht
        have ht_half_lt : t / 2 < t := by linarith
        have hseries : ContDiffAt ℝ 2
            (fun q : ℝ × ℝ =>
              ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
                cosineCoeffs (intervalDomainLift u₀) k) *
                cosineMode k q.2)
            (t, y) :=
          ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
            _hu₀_bound ht_half_pos ht_half_lt
        apply hseries.congr_of_eventuallyEq
        have hset : Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 ∈ 𝓝 (t, y) :=
          IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_Ioo) ⟨ht, hy⟩
        filter_upwards [hset] with q hq
        obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
        have hq1' : 0 < q.1 := hq1
        have hq2_cc : q.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hq2
        symm
        trans (unitIntervalCosineHeatValue q.1 (heatCoeff u₀) q.2)
        · simpa [u] using
            ShenWork.IntervalPicardLevel0SourceTimeC1On.heatSlice_profile_eq_heatValue
              p hq1' _hu₀_cont _hu₀_bound hq2_cc
        · simp only [unitIntervalCosineHeatValue,
            unitIntervalCosineHeatPointWeight,
            unitIntervalCosineMode_eq_cosineMode,
            heatCoeff]
          congr 1
          ext k
          ring

      -- 3C: resolver value joint C² from PhysicalResolverJointC2Data.
      have hv_c2 : ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
          (r, x) := by
        simpa [u] using
          (ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_jointContDiffAt_two
            (p := p) (u := conjugatePicardIter p u₀ 0) (H := Hphys)
            (s := r) (x := x) hx)

      -- 3D: resolver spatial-gradient joint C² from PhysicalResolverJointC2Data.
      have hgradv_c2 : ContDiffAt ℝ 2
          (fun q : ℝ × ℝ =>
            deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
          (r, x) := by
        simpa [u] using
          (ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_grad_jointContDiffAt_two
            (p := p) (u := conjugatePicardIter p u₀ 0) (H := Hphys)
            (s := r) (x := x) hx)

      -- Joint C² of the lifted flux at `(r,x)` from u/v/∂ₓv C² and the floor.
      have hflux_c2 : ContDiffAt ℝ 2
          (Function.uncurry (coupledChemDivFluxLift p u)) (r, x) :=
        ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_contDiffAt_of_factorJointC2
          hu_c2_rx hv_c2 hgradv_c2 hbase_u

      -- The pointwise floor `hbase` gives an eventual-in-space floor by continuity
      -- of the resolver value at `(r,x)`.
      have hbase_event_y : ∀ᶠ y in 𝓝 x,
          0 < 1 + intervalDomainLift (coupledChemicalConcentration p u r) y := by
        have hv_slice_cont : ContinuousAt
            (fun y : ℝ => intervalDomainLift (coupledChemicalConcentration p u r) y) x := by
          have hpath : ContinuousAt (fun y : ℝ => (r, y)) x :=
            (continuousAt_const : ContinuousAt (fun _ : ℝ => r) x).prod continuousAt_id
          simpa [Function.comp_def] using hv_c2.continuousAt.comp x hpath
        have hden_cont : ContinuousAt
            (fun y : ℝ => 1 + intervalDomainLift (coupledChemicalConcentration p u r) y) x := by
          simpa using (continuousAt_const.add hv_slice_cont)
        simpa only [Set.mem_Ioi] using hden_cont (isOpen_Ioi.mem_nhds hbase_u)

      -- The same floor, now eventual in time at fixed `x`; this is needed for the
      -- spatial derivative / fderiv bridge around `r`.
      have hbase_event_t : ∀ᶠ t in 𝓝 r,
          0 < 1 + intervalDomainLift (coupledChemicalConcentration p u t) x := by
        have hv_time_cont : ContinuousAt
            (fun t : ℝ => intervalDomainLift (coupledChemicalConcentration p u t) x) r := by
          have hpath : ContinuousAt (fun t : ℝ => (t, x)) r :=
            continuousAt_id.prod
              (continuousAt_const : ContinuousAt (fun _ : ℝ => x) r)
          simpa [Function.comp_def] using hv_c2.continuousAt.comp r hpath
        have hden_cont : ContinuousAt
            (fun t : ℝ => 1 + intervalDomainLift (coupledChemicalConcentration p u t) x) r := by
          simpa using (continuousAt_const.add hv_time_cont)
        simpa only [Set.mem_Ioi] using hden_cont (isOpen_Ioi.mem_nhds hbase_u)

      -- Spatial derivative of a fixed-time flux slice equals the `(0,1)` fderiv
      -- of the uncurried flux, eventually in the time variable.
      have hspatial :
          (fun t : ℝ => deriv (coupledChemDivFluxLift p u t) x) =ᶠ[𝓝 r]
            (fun t : ℝ =>
              fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
                (t, x) (0, 1)) := by
        have ht_pos_event : Ioi (0 : ℝ) ∈ 𝓝 r := isOpen_Ioi.mem_nhds hr_pos'
        filter_upwards [hbase_event_t, ht_pos_event] with t htbase htpos
        have htpos' : 0 < t := htpos
        have hu_t : ContDiffAt ℝ 2
            (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (t, x) :=
          hu_c2_at htpos' hx
        have hv_t : ContDiffAt ℝ 2
            (fun q : ℝ × ℝ =>
              intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
            (t, x) := by
          simpa [u] using
            (ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_jointContDiffAt_two
              (p := p) (u := conjugatePicardIter p u₀ 0) (H := Hphys)
              (s := t) (x := x) hx)
        have hgradv_t : ContDiffAt ℝ 2
            (fun q : ℝ × ℝ =>
              deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
            (t, x) := by
          simpa [u] using
            (ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_grad_jointContDiffAt_two
              (p := p) (u := conjugatePicardIter p u₀ 0) (H := Hphys)
              (s := t) (x := x) hx)
        have hflux_t : ContDiffAt ℝ 2
            (Function.uncurry (coupledChemDivFluxLift p u)) (t, x) :=
          ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_contDiffAt_of_factorJointC2
            hu_t hv_t hgradv_t htbase
        have hdiff_t : DifferentiableAt ℝ
            (Function.uncurry (coupledChemDivFluxLift p u)) (t, x) :=
          hflux_t.differentiableAt (by norm_num)
        simpa [Function.uncurry] using
          ShenWork.IntervalCoupledRegularityBootstrap.real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
            hdiff_t

      -- Eventual local inputs for the time-partial bridge.  These are the local
      -- version of the hypotheses packaged globally by
      -- `coupledChemDivFlux_timeBridge_of_physicalJointC2`.
      have hu_event : ∀ᶠ y in 𝓝 x,
          ContDiffAt ℝ 2
            (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (r, y) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hu_c2_at hr_pos' hy

      have hv_event : ∀ᶠ y in 𝓝 x,
          ContDiffAt ℝ 2
            (fun q : ℝ × ℝ =>
              intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
            (r, y) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        simpa [u] using
          (ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_jointContDiffAt_two
            (p := p) (u := conjugatePicardIter p u₀ 0) (H := Hphys)
            (s := r) (x := y) hy)

      have hgradv_event : ∀ᶠ y in 𝓝 x,
          ContDiffAt ℝ 2
            (fun q : ℝ × ℝ =>
              deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
            (r, y) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        simpa [u] using
          (ShenWork.IntervalResolverJointC2PhysicalConcrete.coupledChemical_grad_jointContDiffAt_two
            (p := p) (u := conjugatePicardIter p u₀ 0) (H := Hphys)
            (s := r) (x := y) hy)

      have hgv_event : ∀ᶠ y in 𝓝 x,
          HasDerivAt
            (fun t : ℝ =>
              deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y)
            (deriv (coupledChemicalTimeDerivativeLift p u r) y) r := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        simpa [u] using
          (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemical_innerCommute_of_physicalJointC2
            (p := p) (u := conjugatePicardIter p u₀ 0) (H := Hphys)
            (s := r) (y := y) hy)

      -- 3F: the explicit flux time derivative equals the `(1,0)` fderiv partial,
      -- eventually in space.
      have htime :
          (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u r y) =ᶠ[𝓝 x]
            (fun y : ℝ =>
              fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
                (r, y) (1, 0)) :=
        ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
          (p := p) (u := u) (s := r) (x := x)
          (hu := hu_event) (hv := hv_event) (hgradv := hgradv_event)
          (hbase := hbase_event_y) (hgv := hgv_event)

      -- Outer commute: ∂ₜ∂ₓ flux = ∂ₓ∂ₜ flux, by the committed Clairaut bridge.
      have houter : HasDerivAt
          (fun t : ℝ => deriv (coupledChemDivFluxLift p u t) x)
          (deriv (coupledChemDivFluxTimeDerivativeLift p u r) x) r :=
        ShenWork.IntervalCoupledRegularityBootstrap.real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
          (F := coupledChemDivFluxLift p u)
          (Ft := coupledChemDivFluxTimeDerivativeLift p u)
          hflux_c2 hspatial htime

      -- Convert back from flux notation to the source/time-derivative notation.
      have hsource_eq :
          (fun t : ℝ => coupledChemDivSourceLift p u t x) =
            fun t : ℝ => deriv (coupledChemDivFluxLift p u t) x := by
        funext t
        exact ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivSourceLift_eq_deriv_fluxLift_interior
          (p := p) (u := u) (s := t) (x := x) hx

      simpa [hsource_eq,
        ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative]
        using houter
```

## Why this is the right local body

This body maps the combined sorry exactly as follows:

```text
3C := coupledChemical_jointContDiffAt_two Hphys
3D := coupledChemical_grad_jointContDiffAt_two Hphys
3F := coupledChemical_innerCommute_of_physicalJointC2 Hphys
      + coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
      + real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
```

The already-proved `_hu_c2_bridged` is used at the base point `(r,x)`, and the helper `hu_c2_at` repeats the same heat bridge for neighboring positive-time/interior points needed by the `=ᶠ` bridge hypotheses. The already-proved `hbase` is used twice: once directly for flux joint C² at `(r,x)`, and twice through continuity to obtain the eventual floor in space and in time.

The proof intentionally does **not** invoke `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs` or the FAC wrapper, because those packages target older/global slab shapes. The current Level0 code wants only this direct positive-time `HasDerivAt` field.
