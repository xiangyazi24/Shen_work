#!/usr/bin/env python3
from __future__ import annotations

import q3343_endpoint_xi_audit as base
import q3343_endpoint_xi_audit_v6 as trusted
import q3343_endpoint_xi_audit_v7 as levels


def main() -> None:
    t10,a10,c10,_,z10=levels.enumerate_levels(10_000)
    print("Q3343 COUNT REPAIR")
    print("qmax_10000_folded_target_pairs",len(t10))
    print("qmax_10000_central_targets_excluded",z10)
    print("qmax_10000_abstract_J_roots",len(a10))
    print("qmax_10000_canonical_support_triples",len(c10))
    print("q3319_failed_pair",(len(a10),len(c10)))
    assert len(a10)==159
    assert len(c10)==78

    targets,abstract,canonical,cmap,central=levels.enumerate_levels(30_000)
    print("qmax_30000_folded_target_pairs",len(targets))
    print("qmax_30000_central_targets_excluded",central)
    print("qmax_30000_abstract_J_roots",len(abstract))
    print("qmax_30000_trusted_beta1_support",len(canonical))
    assert len(targets)==1653
    assert len(canonical)==180

    tuples,used=base.actual_tuples(targets,cmap,30_000)
    print("nmax_30000_actual_tuples",len(tuples))
    print("nmax_30000_actual_support_triples",len(used))
    print("nmax_30000_direct_tuples",sum(r[-1]=="D" for r in tuples))
    print("nmax_30000_reflected_tuples",sum(r[-1]=="R" for r in tuples))
    assert len(tuples)==34
    assert len(used)==13

    certs=[]; simultaneous=[]
    for J,j,q in canonical:
        Xi,beta2,H,Xia=trusted.certificate(J,j,q)
        if Xi==0 or beta2==0:
            simultaneous.append((J,j,q,Xi,beta2))
        else:
            certs.append((J,j,q,Xi,base.inv(Xi,q),beta2,H,Xia))
    print("simultaneous_beta1_beta2_target_zero",len(simultaneous))
    assert simultaneous==[]
    assert len(certs)==180

    print("ACTUAL_SUPPORT_TRIPLES")
    for r in used: print(*r)
    print("ACTUAL_TUPLES columns=n q J L j branch")
    for r in tuples: print(*r)
    print("ENDPOINT_CERTIFICATES columns=J j q Xi XiInverse beta2 Hboundary XiCompanion")
    for r in certs: print(*r)
    print("first_counterexample=None")
    print("all_assertions_passed=True")

if __name__=="__main__":
    main()
