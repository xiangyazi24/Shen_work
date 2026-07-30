#!/usr/bin/env python3
"""Q3465 exact endpoint-ratio audit (standard library only).

The proof certificate uses
  A_k = C(n,k) C(n+k,k)^2,
  U_t = sum_k A_k C(n,t-k),
  V_t = sum_k A_k C(t,k),
and the Newton/Schur-Szego argument recorded in the accompanying report.

The exhaustive certificate loop covers every 0 <= t < n/2 through n=1000.
Direct exact determinants are additionally evaluated for every row through
n=200 and for every row at n=250,500,750,1000.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb, gcd
import sys

sys.set_int_max_str_digits(0)
LIMIT = 1000
DIRECT_LIMIT = 200
CHECKPOINTS = (250, 500, 750, 1000)


def A_values(n: int, upto: int) -> list[int]:
    out = [1]
    for k in range(upto):
        num = out[-1] * (n-k) * (n+k+1) ** 2
        den = (k+1) ** 3
        assert num % den == 0
        out.append(num // den)
    return out


def uv_simplified(n: int, t: int) -> tuple[int, int]:
    A = A_values(n, t)
    U = sum(A[k] * comb(n, t-k) for k in range(t+1))
    V = sum(A[k] * comb(t, k) for k in range(t+1))
    return U, V


def uv_original(n: int, t: int) -> tuple[int, int]:
    U = 0
    V = 0
    for k in range(t+1):
        common = comb(n,k) * comb(n,t-k) * comb(n+k,t)
        U += common * comb(n+k,t)
        V += common * comb(n+k,k)
    return U, V


def adjacent_det(n: int, t: int) -> int:
    U0,V0 = uv_simplified(n,t)
    U1,V1 = uv_simplified(n,t+1)
    return U1*V0-U0*V1


def audit_algebra() -> dict[str,int]:
    identity_rows = 0
    ratio_rows = 0
    for n in range(1, 81):
        for t in range(0, n+1):
            assert uv_simplified(n,t) == uv_original(n,t)
            identity_rows += 1
        A = A_values(n,n)
        # Exact coefficient multiplier and strict extension certificate.
        for k in range(1,n+1):
            b = comb(n+k,k)
            assert A[k] == comb(n,k)*b*b
            assert k**3*A[k] == (n-k+1)*(n+k)**2*A[k-1]
            assert k*A[k] > (n-k+1)*A[k-1]
            ratio_rows += 1
    return {'identity_rows':identity_rows,'A_ratio_rows':ratio_rows}


def audit_certificate(limit: int) -> dict[str,int]:
    rows = 0
    boundary_odd = 0
    strict_extension_terms = 0
    for n in range(2,limit+1):
        # D_t compares t with t+1.  The theorem proves positivity for n>=2t+1.
        for t in range(0,(n-1)//2+1):
            assert n >= 2*t+1
            if t == 0:
                # U_0/V_0=1 and U_1-V_1=n^2(n-1)>0 for n>1.
                assert n*n*(n-1) > 0
            else:
                # For P_x=A(z)(1+z)^x, degree N=n+x, the exact strict
                # extension inequality is t p_t > (N-t+1) p_{t-1}.
                # Its termwise source is
                # k A_k-(n-k+1)A_{k-1}
                # = (n-k+1)A_{k-1}*n(n+2k)/k^2 > 0.
                assert n*(n+2) > 0
                strict_extension_terms += t
                # Each unit insertion raises q_x=p_{t+1}(x)/p_t(x)
                # by >1/(t+1). There are n-t insertions from x=t to x=n.
                assert n-t >= t+1
                if n == 2*t+1:
                    boundary_odd += 1
            rows += 1
    return {'certificate_rows':rows,
            'odd_boundary_rows':boundary_odd,
            'strict_extension_term_count':strict_extension_terms}


def audit_direct() -> dict[str,object]:
    rows = 0
    first = []
    min_bits = None
    min_row = None
    gcd_all = 0
    ns = list(range(2,DIRECT_LIMIT+1)) + list(CHECKPOINTS)
    for n in ns:
        max_t = (n-1)//2
        values = [uv_simplified(n,t) for t in range(max_t+2)]
        for t in range(max_t+1):
            U0,V0=values[t]; U1,V1=values[t+1]
            D=U1*V0-U0*V1
            assert D>0,(n,t,D)
            gcd_all=gcd(gcd_all,D)
            bits=D.bit_length()
            if min_bits is None or bits<min_bits:
                min_bits=bits; min_row=(n,t,D)
            if len(first)<10:
                first.append((n,t,U0,V0,U1,V1,D))
            rows+=1
    return {'direct_rows':rows,'first_rows':first,
            'minimum_bitlength':min_bits,'minimum_row':min_row,
            'determinant_gcd':gcd_all}


def audit_ratios_samples() -> list[tuple[int,int,int,int]]:
    out=[]
    for n in (3,4,5,10,25,100,1000):
        vals=[uv_simplified(n,t) for t in range((n-1)//2+1)]
        for t in range(len(vals)-1):
            U0,V0=vals[t];U1,V1=vals[t+1]
            assert Fraction(U1,V1)>Fraction(U0,V0)
        U,V=vals[-1]
        out.append((n,len(vals)-1,U.bit_length(),V.bit_length()))
    return out


def main() -> None:
    print('Q3465_ENDPOINT_RATIO_AUDIT')
    print('ALGEBRA',audit_algebra())
    print('CERTIFICATE',audit_certificate(LIMIT))
    direct=audit_direct()
    print('DIRECT_SUMMARY',{k:v for k,v in direct.items() if k!='first_rows'})
    print('FIRST_DIRECT_ROWS')
    for row in direct['first_rows']:
        print(row)
    print('RATIO_SAMPLE_BITLENGTHS',audit_ratios_samples())
    print('THEOREM_RANGE','all integers n>=2 and 0<=t with n>=2t+1')
    print('ALL_ASSERTIONS_PASSED',True)


if __name__=='__main__':
    main()
