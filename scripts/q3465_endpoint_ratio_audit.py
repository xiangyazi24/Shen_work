#!/usr/bin/env python3
"""Q3465 endpoint-ratio audit after the universal conjecture fails.

Standard library only.  The program:
  * evaluates U_t,V_t from their original exact sums using hypergeometric
    term recurrences;
  * certifies the first counterexample (n,t)=(6,2);
  * scans the full requested range through n=220;
  * audits the strongest surviving numerical range n>=3t+1 through n=1000;
  * checks all five currently known a=3 simultaneous-target geometries.
No numerical range is promoted to a theorem by the program alone.
"""
from __future__ import annotations

from math import comb
from hashlib import sha256
import sys

sys.set_int_max_str_digits(0)
FULL_LIMIT = 220
RANGE_LIMIT = 1000
KNOWN_A3 = [
    (740,152,110),
    (1664,374,170),
    (5515,1051,49),
    (7319,1781,431),
    (8241,1011,51),
]


def uv(n: int, t: int) -> tuple[int,int]:
    assert 0 <= t <= n
    c = comb(n,t)
    u = c*c*c
    v = c*c
    U,V = u,v
    for k in range(t):
        u_num = u*(n-k)*(t-k)*(n+k+1)**2
        u_den = (k+1)*(n-t+k+1)**3
        assert u_num % u_den == 0
        u = u_num//u_den
        v_num = v*(n-k)*(t-k)*(n+k+1)**2
        v_den = (k+1)**2*(n-t+k+1)**2
        assert v_num % v_den == 0
        v = v_num//v_den
        U += u
        V += v
    return U,V


def uv_direct(n: int,t: int) -> tuple[int,int]:
    U=sum(comb(n,k)*comb(n,t-k)*comb(n+k,t)**2 for k in range(t+1))
    V=sum(comb(n,k)*comb(n,t-k)*comb(n+k,t)*comb(n+k,k) for k in range(t+1))
    return U,V


def det_adj(n: int,t: int) -> tuple[int,tuple[int,int],tuple[int,int]]:
    a=uv(n,t); b=uv(n,t+1)
    return b[0]*a[1]-a[0]*b[1],a,b


def digest(x:int)->str:
    return sha256(str(abs(x)).encode('ascii')).hexdigest()


def audit_identity() -> int:
    rows=0
    for n in range(1,51):
        for t in range(n+1):
            assert uv(n,t)==uv_direct(n,t)
            rows+=1
    return rows


def audit_first_counterexample() -> dict[str,object]:
    first=None
    rows=0
    failures=[]
    for n in range(3,FULL_LIMIT+1):
        for t in range(1,(n-2)//2+1):
            D,a,b=det_adj(n,t)
            rows+=1
            if D<=0:
                failures.append((n,t,D.bit_length() if D else 0,digest(D)))
                if first is None:
                    first=(n,t,D,a,b)
    assert first is not None
    assert first[:2]==(6,2),first[:2]
    assert first[2]==-91345620,first[2]
    assert first[3]==(31011,17277)
    assert first[4]==(541610,304690)
    return {'rows':rows,'failure_count':len(failures),
            'first':first,'first_ten_failures':failures[:10]}


def audit_three_to_one_range() -> dict[str,object]:
    rows=0
    first_failure=None
    boundary_rows=0
    min_bits=None
    min_row=None
    for n in range(4,RANGE_LIMIT+1):
        for t in range(1,(n-1)//3+1):
            D,a,b=det_adj(n,t)
            rows+=1
            if n==3*t+1:
                boundary_rows+=1
            if D<=0 and first_failure is None:
                first_failure=(n,t,D,a,b)
            if D>0:
                bits=D.bit_length()
                if min_bits is None or bits<min_bits:
                    min_bits=bits;min_row=(n,t,D)
    assert first_failure is None,first_failure
    return {'rows':rows,'boundary_rows':boundary_rows,
            'first_failure':first_failure,
            'minimum_positive_bitlength':min_bits,
            'minimum_positive_row':min_row}


def audit_known_targets() -> list[tuple[int,int,int,int,str]]:
    out=[]
    for n,r,s in KNOWN_A3:
        Ur,Vr=uv(n,r); Us,Vs=uv(n,s)
        D=Ur*Vs-Vr*Us
        assert 0<s<r and 4*r<n
        assert D>0,(n,r,s,D)
        out.append((n,r,s,D.bit_length(),digest(D)))
    return out


def t_one_polynomial_certificate(n:int)->int:
    P=2*n**6-2*n**5-19*n**4-n**3-5*n**2-9*n-6
    D,_,_=det_adj(n,1)
    assert 8*D==n**3*P
    m=n-4
    shifted=(2*m**6+46*m**5+421*m**4+1935*m**3+
             4559*m**2+4767*m+1094)
    assert P==shifted
    return D


def main()->None:
    print('Q3465_ENDPOINT_RATIO_REPAIR')
    print('IDENTITY_ROWS',audit_identity())
    print('FIRST_COUNTEREXAMPLE_AUDIT',audit_first_counterexample())
    print('PROVED_T1_SAMPLE',[(n,t_one_polynomial_certificate(n)) for n in range(4,11)])
    print('THREE_TO_ONE_RANGE_AUDIT',audit_three_to_one_range())
    print('KNOWN_A3_TARGETS',audit_known_targets())
    print('STATUS','universal half-range conjecture false; t=1 proved; n>=3t+1 is exact numerical conjecture through 1000')
    print('ALL_ASSERTIONS_PASSED',True)


if __name__=='__main__':
    main()
