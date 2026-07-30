#!/usr/bin/env python3
from __future__ import annotations

import q3343_endpoint_xi_audit as base


def carrier_roots(q: int, j: int, b: list[int]):
    maxJ=(q-2)//2
    assert 1<=j<=maxJ and b[j]==0 and b[j-1]!=0
    d1,_,_=base.derivative_rows(j,j,q)
    g=base.green_state(j,j,q)
    beta1=base.dot(d1,g,q)
    D=beta1*b[j-1]%q
    roots=[j] if D==0 else []
    if j==maxJ: return roots
    f=base.franel_mod(q,maxJ)
    fac,ifac=base.factorials_mod(q,2*maxJ+1)
    h=fac[2*j]*ifac[j+1]%q*ifac[j+1]%q  # p'_(j+1)(lambda_j)
    for K in range(j+1,maxJ+1):
        D=(D+f[K]*h)%q
        if D==0: roots.append(K)
        if K<maxJ:
            h=(-h*(K-j)*(K+j+1)*base.inv((K+1)**2,q))%q
    return roots


def enumerate_support(qmax: int):
    targets=[]; support=[]; support_map={}; central=0
    for q in base.primes_upto(qmax):
        if q<5: continue
        half=(q-1)//2
        b=base.apery_mod(q,half)
        for j in range(1,half+1):
            if b[j]!=0: continue
            targets.append((q,j))
            if j>=(q-1)//2:
                central+=1
                continue
            for J in carrier_roots(q,j,b):
                key=(J,j,q)
                assert key not in support_map
                support_map[key]=1
                support.append(key)
    return sorted(targets),sorted(support),support_map,central


def certificate(J: int,j: int,q: int):
    b=base.apery_mod(q,J)
    a=base.companion_mod(q,J)
    d1,d2,H=base.derivative_rows(J,j,q)
    g=base.green_state(J,j,q)
    beta1=base.dot(d1,g,q)
    beta2=base.dot(d2,g,q)
    rb=base.dot(d1,b,q); sb=base.dot(d2,b,q)
    ra=base.dot(d1,a,q); sa=base.dot(d2,a,q)
    Rb=(2*j+1)*rb%q
    Cb=(2*j+1)*sb%q
    Xi_b=(Cb-2*H*Rb)%q
    Ra=(2*j+1)*ra%q
    Ca=(2*j+1)*sa%q
    Xi_a=(Ca-2*H*Ra)%q
    assert b[j]==0 and b[j-1]!=0
    assert beta1==0 and Rb==0
    assert rb==beta1*b[j-1]%q
    assert sb==beta2*b[j-1]%q
    lhs=j**3*(a[j]*Xi_b-b[j]*Xi_a)%q
    rhs=6*(2*j+1)*(beta2-2*H*beta1)%q
    assert lhs==rhs
    return Xi_b,beta2,H,Xi_a


def main() -> None:
    t10,s10,_,c10=enumerate_support(10_000)
    print("Q3343 COUNT REPAIR")
    print("qmax_10000_folded_target_pairs",len(t10))
    print("qmax_10000_central_targets_excluded",c10)
    print("qmax_10000_trusted_beta1_support",len(s10))
    # This is the count Q3319 incorrectly asserted to be 78.
    print("q3319_failed_pair",(159,78))
    assert len(s10)==159

    targets,support,support_map,central=enumerate_support(30_000)
    print("qmax_30000_folded_target_pairs",len(targets))
    print("qmax_30000_central_targets_excluded",central)
    print("qmax_30000_trusted_beta1_support",len(support))
    assert len(targets)==1653
    assert len(support)==180

    tuples,used=base.actual_tuples(targets,support_map,30_000)
    print("nmax_30000_actual_tuples",len(tuples))
    print("nmax_30000_actual_support_triples",len(used))
    print("nmax_30000_direct_tuples",sum(r[-1]=="D" for r in tuples))
    print("nmax_30000_reflected_tuples",sum(r[-1]=="R" for r in tuples))
    assert len(tuples)==34
    assert len(used)==13

    certs=[]; simultaneous=[]
    for J,j,q in support:
        Xi,beta2,H,Xia=certificate(J,j,q)
        if beta2==0 or Xi==0:
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
