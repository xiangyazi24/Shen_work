#!/usr/bin/env python3
from __future__ import annotations

import q3343_endpoint_xi_audit as base
import q3343_endpoint_xi_audit_v2 as audit2
import q3343_endpoint_xi_audit_v4 as fixed

base.endpoint_and_roots=fixed.endpoint_and_roots_all_high_shells


def main() -> None:
    targets10,support10,map10,central10=audit2.enumerate_support(10_000)
    print("Q3343 COUNT REPAIR")
    print("qmax_10000_folded_target_pairs",len(targets10))
    print("qmax_10000_central_folded_targets_excluded",central10)
    print("qmax_10000_unique_abstract_support_triples",len(support10))
    assert len(support10)==159

    targets,support,support_map,central=audit2.enumerate_support(base.QMAX)
    print("qmax_30000_folded_target_pairs",len(targets))
    print("qmax_30000_central_folded_targets_excluded",central)
    print("qmax_30000_unique_beta1_support_triples",len(support))
    assert len(targets)==1653
    assert len(support)==180

    tuples,used=base.actual_tuples(targets,support_map,base.NMAX)
    print("nmax_30000_actual_tuples",len(tuples))
    print("nmax_30000_actual_support_triples",len(used))
    print("nmax_30000_direct_tuples",sum(row[-1]=="D" for row in tuples))
    print("nmax_30000_reflected_tuples",sum(row[-1]=="R" for row in tuples))
    assert len(tuples)==34
    assert len(used)==13

    certificates=[]; simultaneous=[]
    for J,j,q,C in support:
        if C==0:
            simultaneous.append((J,j,q))
        else:
            certificates.append((J,j,q,*base.exact_endpoint_certificate(J,j,q,C)))
    print("simultaneous_beta1_beta2_target_zero",len(simultaneous))
    assert simultaneous==[]
    assert len(certificates)==180

    print("ACTUAL_SUPPORT_TRIPLES")
    for row in used: print(*row)
    print("ACTUAL_TUPLES columns=n q J L j branch")
    for row in tuples: print(*row)
    print("ENDPOINT_CERTIFICATES columns=J j q Xi XiInverse beta2 Hboundary XiCompanion")
    for row in certificates: print(*row)
    print("first_counterexample=None")
    print("all_assertions_passed=True")

if __name__=="__main__":
    main()
