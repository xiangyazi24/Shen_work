#!/usr/bin/env python3
"""Q3443: exact a=3 fixed-moment shell audit.

Standard library only. It reconstructs the exact k=1,2,3 packets, audits every
same-block a=3 pair through M<=600, and scans genuine simultaneous target pairs
through n<=10000.
"""
from __future__ import annotations

from collections import Counter
from hashlib import sha256
from math import comb, gcd, isqrt
import sys

sys.set_int_max_str_digits(0)
SMALL_LIMIT = 600
TARGET_LIMIT = 10_000


def primes_upto(n: int) -> list[bool]:
    mark = bytearray(b"\x01") * (n + 1)
    if n >= 0: mark[0] = 0
    if n >= 1: mark[1] = 0
    for p in range(2, isqrt(n) + 1):
        if mark[p]:
            mark[p*p:n+1:p] = b"\x00" * (((n-p*p)//p)+1)
    return [bool(x) for x in mark]


def apery_values(nmax: int) -> list[int]:
    if nmax == 0: return [1]
    b = [1, 5]
    for n in range(1, nmax):
        P = 34*n**3 + 51*n**2 + 27*n + 5
        num = P*b[n] - n**3*b[n-1]
        den = (n+1)**3
        assert num % den == 0
        b.append(num//den)
    return b


def binomial_row(n: int) -> list[int]:
    row = [1]*(n+1)
    for k in range(n):
        row[k+1] = row[k]*(n-k)//(k+1)
    return row


def cyclic_shell(M: int, spacing: int, row_M: list[int] | None = None) -> int:
    assert spacing >= 1
    if row_M is None: row_M = binomial_row(M)
    residues = [0]*spacing
    for k, value in enumerate(row_M):
        residues[k % spacing] += value
    radius = M//spacing
    states = {j: (row_M[j*spacing] if j >= 0 else 0)
              for j in range(-radius, radius+1)}
    total = 0
    for t in range(M+1):
        moving = sum(states.values())
        total += row_M[t]*residues[t % spacing]*moving*moving
        if t == M: break
        nxt = {}
        for j, value in states.items():
            activation = -j*spacing
            if j < 0 and t+1 == activation:
                nxt[j] = 1
            elif t >= activation:
                den = t + j*spacing + 1
                assert den > 0
                num = value*(M+t+1)
                assert num % den == 0
                nxt[j] = num//den
            else:
                nxt[j] = 0
        states = nxt
    return total


def packet_data(M: int, m: int, bM: int, row_M: list[int] | None = None):
    assert 3*m < M < 4*m
    if row_M is None: row_M = binomial_row(M)
    C1 = cyclic_shell(M, m, row_M)
    C2 = cyclic_shell(M, 2*m, row_M)
    C3 = cyclic_shell(M, 3*m, row_M)
    P3 = C3-bM
    P2 = C2-bM
    P1 = C1-bM-P2-P3
    assert min(P1,P2,P3) > 0
    assert C1 == bM+P1+P2+P3
    return C1,P1,P2,P3


def admissible_scales(M: int) -> range:
    return range((M+4)//4, (M-1)//3+1)


def choose(n: int, k: int) -> int:
    return comb(n,k) if 0 <= k <= n else 0


def coefficient_formula(M: int, u: int, v: int, w: int) -> int:
    return sum(comb(M,t)*choose(M,u+M-t)
               *choose(2*M-t,v+M-t)*choose(2*M-t,w+M-t)
               for t in range(M+1))


def scaled_vectors():
    out=[]
    for a in range(-3,4):
        for b in range(-3,4):
            for c in range(-3,4):
                if (a,b,c)==(0,0,0): continue
                g=gcd(gcd(abs(a),abs(b)),abs(c))
                assert g in (1,2,3)
                out.append((a,b,c,g))
    return out

VECTORS=scaled_vectors()


def sign(x:int)->int: return (x>0)-(x<0)

def digest(x:int)->str: return sha256(str(abs(x)).encode()).hexdigest()


def edge_ledger(M:int,d:int,e:int,top:int=12):
    q,ell=d+1,e+1
    edges=[]; sums={1:0,2:0,3:0}
    for a,b,c,g in VECTORS:
        left=coefficient_formula(M,d*a,d*b,d*c)
        right=coefficient_formula(M,e*a,e*b,e*c)
        value=ell*left-q*right
        sums[g]+=value
        edges.append((value,(a,b,c),g,left,right))
    edges.sort(key=lambda x:x[0])
    return sums,edges[:top],list(reversed(edges[-top:]))


def direct_small_check():
    from collections import defaultdict
    def mul(A,B):
        C=defaultdict(int)
        for u,x in A.items():
            for v,y in B.items():
                C[(u[0]+v[0],u[1]+v[1],u[2]+v[2])]+=x*y
        return dict(C)
    one={(0,0,0):1}; x={(0,0,0):1,(1,0,0):1}
    y={(0,0,0):1,(0,1,0):1}; z={(0,0,0):1,(0,0,1):1}
    yz=mul(y,z); bracket=dict(yz); bracket[(1,1,1)]=bracket.get((1,1,1),0)+1
    numerator=one
    for factor in (x,y,z,bracket): numerator=mul(numerator,factor)
    Lambda={(u-1,v-1,w-1):c for (u,v,w),c in numerator.items()}
    power=one; rows=0
    for M in range(7):
        row=binomial_row(M)
        for nu,value in power.items():
            assert coefficient_formula(M,*nu)==value; rows+=1
        for d in range(1,M+2):
            exact=sum(c for nu,c in power.items() if all(x%d==0 for x in nu))
            assert cyclic_shell(M,d,row)==exact; rows+=1
        power=mul(power,Lambda)
    return rows


def audit_small_range(b,prime):
    pair_count=prime_pair_count=0
    total_signs=Counter(); packet_signs=Counter(); negative_driver=Counter()
    zero_rows=[]; prime_zero_rows=[]; first_negative=None; first_prime_negative=None
    first_packet_negative={}
    for M in range(5,SMALL_LIMIT+1):
        scales=list(admissible_scales(M))
        if len(scales)<2: continue
        row=binomial_row(M)
        data={d:packet_data(M,d,b[M],row) for d in scales}
        for ix,d in enumerate(scales):
            Cd,*Pd=data[d]
            for e in scales[ix+1:]:
                Ce,*Pe=data[e]; q,ell=d+1,e+1; h=e-d
                center=h*b[M]
                pieces=[ell*Pd[k]-q*Pe[k] for k in range(3)]
                numerator=ell*Cd-q*Ce
                assert numerator==center+sum(pieces)
                pair_count+=1; total_signs[sign(numerator)]+=1
                packet_signs[tuple(sign(x) for x in pieces)]+=1
                for k,x in enumerate(pieces,1):
                    if x<0 and k not in first_packet_negative:
                        first_packet_negative[k]=(M,d,e,x)
                if numerator<0:
                    negative_driver[min(range(3),key=lambda k:pieces[k])+1]+=1
                    if first_negative is None: first_negative=(M,d,e,numerator,center,*pieces)
                if numerator==0: zero_rows.append((M,d,e))
                if prime[q] and prime[ell]:
                    prime_pair_count+=1
                    if numerator<0 and first_prime_negative is None:
                        first_prime_negative=(M,q,ell,numerator)
                    if numerator==0: prime_zero_rows.append((M,q,ell))
    assert first_negative and first_negative[:3]==(90,26,27), first_negative
    return dict(pair_count=pair_count,prime_pair_count=prime_pair_count,
                total_signs=dict(total_signs),packet_signs=dict(packet_signs),
                negative_driver=dict(negative_driver),zero_rows=zero_rows,
                prime_zero_rows=prime_zero_rows,first_negative=first_negative,
                first_prime_negative=first_prime_negative,
                first_packet_negative=first_packet_negative)


def witt_digits(N:int,d:int,b):
    r=N-3*d; assert 3<=r<d
    values=[cyclic_shell(r+a*d,d) for a in range(4)]
    assert values[0]==b[r]
    q=d+1
    n1=values[1]-values[0]
    n2=values[2]-2*values[1]+values[0]
    n3=values[3]-3*values[2]+3*values[1]-values[0]
    assert n1%q==0 and n2%(q*q)==0 and n3%(q**3)==0
    D1,D2,D3=n1//q,n2//(q*q),n3//(q**3)
    assert values[3]==b[r]+3*q*D1+3*q*q*D2+q**3*D3
    return values[3],D1,D2,D3


def audit_targets(b,prime):
    target_scale_count=simultaneous_count=target_M_count=witt_rows=0
    signs=Counter(); delta_gcd=0; zero_rows=[]; negative_rows=[]; all_rows=[]
    first_negative=None; min_abs=None; lower=[]
    for M in range(5,TARGET_LIMIT+1):
        targets=[]
        for d in admissible_scales(M):
            q=d+1
            if prime[q]:
                r=M-3*d
                if b[r]%q==0: targets.append(d)
        target_scale_count+=len(targets)
        if len(targets)<2: continue
        target_M_count+=1
        rowM=binomial_row(M)
        data={d:packet_data(M,d,b[M],rowM) for d in targets}
        for ix,d in enumerate(targets):
            q=d+1; Cd,*Pd=data[d]; r=M-3*d
            assert Cd%q==0
            if r>=3:
                Ccheck,D1,D2,D3=witt_digits(M,d,b)
                assert Ccheck==Cd
                assert Cd//q==b[r]//q+3*D1+3*q*D2+q*q*D3
                witt_rows+=1
            else: lower.append((M,q,r))
            for e in targets[ix+1:]:
                ell=e+1; Ce,*Pe=data[e]; s=M-3*e
                assert Ce%ell==0
                if s>=3:
                    Ccheck,E1,E2,E3=witt_digits(M,e,b)
                    assert Ccheck==Ce
                    assert Ce//ell==b[s]//ell+3*E1+3*ell*E2+ell*ell*E3
                    witt_rows+=1
                else: lower.append((M,ell,s))
                h=e-d
                assert h%2==0 and r-s==3*h
                center=h*b[M]
                pieces=[ell*Pd[k]-q*Pe[k] for k in range(3)]
                numerator=ell*Cd-q*Ce
                assert numerator==center+sum(pieces) and numerator%(q*ell)==0
                delta=numerator//(q*ell)
                simultaneous_count+=1; signs[sign(delta)]+=1
                delta_gcd=gcd(delta_gcd,abs(delta))
                compact=(M,q,ell,r,s,sign(delta),abs(delta).bit_length(),digest(delta))
                all_rows.append(compact)
                if delta==0: zero_rows.append((M,q,ell,r,s))
                if delta<0:
                    negative_rows.append(compact)
                    if first_negative is None:
                        first_negative=(M,d,e,q,ell,r,s,delta,center,*pieces)
                if min_abs is None or abs(delta)<min_abs[0]: min_abs=(abs(delta),compact)
    assert first_negative and first_negative[:7]==(743,196,210,197,211,155,113), first_negative
    return dict(target_scale_count=target_scale_count,target_M_count=target_M_count,
                simultaneous_count=simultaneous_count,target_signs=dict(signs),
                target_delta_gcd=delta_gcd,zero_rows=zero_rows,
                negative_rows=negative_rows,all_rows=all_rows,
                first_negative=first_negative,min_abs=min_abs,
                lower_residue_scales=sorted(set(lower)),witt_rows=witt_rows)


def print_edge_report(label,M,d,e):
    sums,neg,pos=edge_ledger(M,d,e)
    print(label,{"M":M,"d":d,"e":e,"q":d+1,"ell":e+1})
    print(label+"_PACKET_SUMS",sums)
    print(label+"_MOST_NEGATIVE")
    for value,vector,packet,left,right in neg:
        print((vector,packet,value,left,right))
    print(label+"_MOST_POSITIVE")
    for value,vector,packet,left,right in pos:
        print((vector,packet,value,left,right))


def main():
    print("Q3443_A3_AUDIT")
    counts=Counter(g for *_,g in VECTORS)
    print("PACKET_CARDINALITIES",counts)
    assert counts==Counter({1:290,2:26,3:26})
    print("INDEPENDENT_SMALL_ROWS",direct_small_check())
    b=apery_values(TARGET_LIMIT)
    prime=primes_upto(TARGET_LIMIT//3+5)
    small=audit_small_range(b,prime)
    print("SMALL_RANGE_SUMMARY",{k:v for k,v in small.items() if k not in ("packet_signs","zero_rows","prime_zero_rows")})
    print("SMALL_PACKET_SIGN_PATTERNS",small["packet_signs"])
    print("SMALL_ZERO_ROWS",small["zero_rows"])
    print("SMALL_PRIME_ZERO_ROWS",small["prime_zero_rows"])
    f=small["first_negative"]
    print_edge_report("FIRST_UNRESTRICTED_NEGATIVE",f[0],f[1],f[2])
    targets=audit_targets(b,prime)
    print("TARGET_SUMMARY",{k:v for k,v in targets.items() if k not in ("all_rows","negative_rows","first_negative","min_abs")})
    print("TARGET_MIN_ABS",targets["min_abs"])
    print("TARGET_NEGATIVE_ROWS",targets["negative_rows"])
    print("TARGET_ALL_ROWS")
    for row in targets["all_rows"]: print(row)
    f=targets["first_negative"]
    print("FIRST_TARGET_NEGATIVE_COMPACT",f[:7],"delta_bits",abs(f[7]).bit_length(),"delta_sha256",digest(f[7]))
    print("FIRST_TARGET_NEGATIVE_PACKET_NUMERATORS",f[8:])
    print_edge_report("FIRST_TARGET_NEGATIVE",f[0],f[1],f[2])
    print("ZERO_CONCLUSION_THROUGH_LIMIT",{"limit":TARGET_LIMIT,"zeros":targets["zero_rows"]})
    print("ALL_ASSERTIONS_PASSED",True)

if __name__=="__main__": main()
