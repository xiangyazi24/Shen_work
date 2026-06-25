# ChatGPT git-drop (cron1)

## Q305 — Paper 2 Propositions 2.1 / 2.2 / 2.3 / 2.5 status audit

### Executive verdict

I grepped for the exact concrete interval-domain theorem names requested:

```text
intervalDomain_Proposition_2_1
intervalDomain_Proposition_2_2
intervalDomain_Proposition_2_3
intervalDomain_Proposition_2_5
```

I did **not** find concrete theorem symbols with those exact names. By the requested criterion, these are **not closed interval-domain concrete theorems** in the current tree.

I also did not find evidence that the current interval-domain Theorem 1.1 headline consumes any of these `intervalDomain_Proposition_2_N` wrappers. The active Theorem 1.1 routes in the repo are built through local-existence / restart / residual interfaces, not by invoking Proposition 2.1/2.2/2.3/2.5 concrete interval-domain theorems.

So the safe status is:

| Paper proposition | Exact `intervalDomain_Proposition_2_N` concrete theorem? | Status by requested criterion | Carries what? |
|---|---:|---|---|
| Prop. 2.1 | Not found | Open / no concrete interval wrapper found | No exact concrete wrapper found to inspect. |
| Prop. 2.2 | Not found | Open / no concrete interval wrapper found | No exact concrete wrapper found to inspect. |
| Prop. 2.3 | Not found | Open / no concrete interval wrapper found | No exact concrete wrapper found to inspect. |
| Prop. 2.5 | Not found | Open / no concrete interval wrapper found | No exact concrete wrapper found to inspect. |

Prop. 2.4 is different; you already identified it as closed, and this audit did not re-open it.

---

## Dependency direction with Theorem 1.1

From the Theorem 1.1 routes already inspected in this repo:

* The χ₀=0 unconditional interval-domain Theorem 1.1 route goes through the canonical Picard/cone/tower local-existence chain and restart/uniform-local-existence providers.
* The χ₀<0 faithful EWA route goes through `ChiNegDatumUniformConstructionFaithful`, then `CoupledFluxClassicalLocalExistenceResidual`, then the interval-domain Theorem 1.1 residual closeout.
* Neither route is organized as “prove Proposition 2.1/2.2/2.3/2.5, then consume them in Theorem 1.1.”

Therefore, for the concrete Lean architecture currently in the tree, the Proposition 2.N wrappers are **not upstream prerequisites consumed by Theorem 1.1**. They appear to be separate proposition-level targets/residuals rather than the active dependency path for the headline.

Conversely, I also found no concrete `intervalDomain_Proposition_2_N` theorem among 2.1/2.2/2.3/2.5 that consumes Theorem 1.1. Since the exact concrete wrappers were not found, there is no theorem body to classify as downstream of Theorem 1.1.

So the dependency answer is:

```text
Current concrete T1.1 routes do not consume intervalDomain_Proposition_2_1/2_2/2_3/2_5.
No exact concrete intervalDomain_Proposition_2_N theorem among these was found that consumes T1.1.
```

---

## Practical consequence

If your goal is the Paper 2 interval-domain headline, do not block on Propositions 2.1/2.2/2.3/2.5 unless you are explicitly trying to close those proposition statements as separate targets. The active headline architecture is already routed through named local-existence / residual / construction packages.

If your goal is to close the proposition inventory itself, the first action is not to discharge hypotheses of existing concrete wrappers, but to add or locate the missing concrete interval-domain wrappers for:

```lean
intervalDomain_Proposition_2_1
intervalDomain_Proposition_2_2
intervalDomain_Proposition_2_3
intervalDomain_Proposition_2_5
```

or to rename existing differently-named proposition reductions so that they are discoverable under the `intervalDomain_Proposition_2_N` convention.

---

## Caveat

This audit used the exact-name grep requested. Broader `Proposition_2_N` search hits may include abstract statement-layer declarations, docs, route notes, or differently-named residual scaffolds, but I did not find exact concrete interval-domain theorem symbols matching the requested names for 2.1/2.2/2.3/2.5. If a differently named theorem is intended to be the concrete interval-domain proposition, it should be aliased under the `intervalDomain_Proposition_2_N` naming convention to avoid this ambiguity.
