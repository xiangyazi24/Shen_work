#!/usr/bin/env python3
from __future__ import annotations

import q3343_endpoint_xi_audit as base


def enumerate_support(qmax: int):
    folded_pairs = []
    support = []
    support_map = {}
    central_targets = 0
    for q in base.primes_upto(qmax):
        if q < 5:
            continue
        half = (q-1)//2
        b = base.apery_mod(q, half)
        for j in range(1, half+1):
            if b[j] != 0:
                continue
            folded_pairs.append((q,j))
            if 2*j+1 == q:
                central_targets += 1
                continue
            roots = base.endpoint_and_roots(q,j,b)
            for J,C in roots:
                key = (J,j,q)
                assert key not in support_map
                support_map[key] = C
                support.append((J,j,q,C))
    return sorted(folded_pairs),sorted(support),support_map,central_targets


def main() -> None:
    targets10,support10,_,central10 = enumerate_support(10_000)
    print("Q3343 COUNT REPAIR")
    print("qmax_10000_folded_target_pairs",len(targets10))
    print("qmax_10000_central_folded_targets_excluded",central10)
    print("qmax_10000_unique_high_support_triples",len(support10))
    assert len(support10) == 78

    targets,support,support_map,central = enumerate_support(base.QMAX)
    print("qmax_30000_folded_target_pairs",len(targets))
    print("qmax_30000_central_folded_targets_excluded",central)
    print("qmax_30000_unique_beta1_support_triples",len(support))
    assert len(targets) == 1653
    assert len(support) == 180

    tuples,used = base.actual_tuples(targets,support_map,base.NMAX)
    print("nmax_30000_actual_tuples",len(tuples))
    print("nmax_30000_actual_support_triples",len(used))
    assert len(tuples) == 34
    assert len(used) == 13

    certificates = []
    simultaneous = []
    for J,j,q,C in support:
        if C == 0:
            simultaneous.append((J,j,q))
        else:
            certificates.append((J,j,q,*base.exact_endpoint_certificate(J,j,q,C)))
    print("simultaneous_beta1_beta2_target_zero",len(simultaneous))
    assert simultaneous == []
    assert len(certificates) == 180

    print("ACTUAL_SUPPORT_TRIPLES")
    for row in used:
        print(*row)
    print("ACTUAL_TUPLES columns=n q J L j branch")
    for row in tuples:
        print(*row)
    print("ENDPOINT_CERTIFICATES columns=J j q Xi XiInverse beta2 Hboundary XiCompanion")
    for row in certificates:
        print(*row)
    print("first_counterexample=None")
    print("all_assertions_passed=True")


if __name__ == "__main__":
    main()
