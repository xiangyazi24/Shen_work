#!/usr/bin/env python3
"""Single-file standard-library audit for Q3443 (a=3 sector)."""
from __future__ import annotations
from collections import Counter, defaultdict
from hashlib import sha256
from math import comb, gcd, isqrt
import sys
sys.set_int_max_str_digits(0)
SMALL_LIMIT=600; N_LIMIT=10_000; M_LIMIT=N_LIMIT-3

def primes_upto(n):
    s=bytearray(b'\x01')*(n+1); s[:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if s[p]: s[p*p:n+1:p]=b'\x00'*(((n-p*p)//p)+1)
    return [bool(x) for x in s]

def apery_values(nmax):
    if nmax==0:return [1]
    b=[1,5]
    for n in range(1,nmax):
        P=34*n**3+51*n**2+27*n+5
        z=P*b[n]-n**3*b[n-1]; den=(n+1)**3
        assert z%den==0; b.append(z//den)
    return b

def binomial_row(n):
    r=[1]*(n+1)
    for k in range(n):r[k+1]=r[k]*(n-k)//(k+1)
    return r

def cyclic_shell(M,d,row=None):
    if row is None:row=binomial_row(M)
    residues=[0]*d
    for k,x in enumerate(row):residues[k%d]+=x
    R=M//d; state={j:(row[j*d] if j>=0 else 0) for j in range(-R,R+1)}
    total=0
    for t in range(M+1):
        u=sum(state.values()); total+=row[t]*residues[t%d]*u*u
        if t==M:break
        nxt={}
        for j,x in state.items():
            a=-j*d
            if j<0 and t+1==a:nxt[j]=1
            elif t>=a:
                den=t+j*d+1; z=x*(M+t+1)
                assert den>0 and z%den==0; nxt[j]=z//den
            else:nxt[j]=0
        state=nxt
    return total

def admissible_scales(M):return range((M+4)//4,(M-1)//3+1)
def packet_data(M,d,bM,row=None):
    assert 3*d<M<4*d
    if row is None:row=binomial_row(M)
    C=cyclic_shell(M,d,row); C2=cyclic_shell(M,2*d,row); C3=cyclic_shell(M,3*d,row)
    P3=C3-bM; P2=C2-bM; P1=C-bM-P2-P3
    assert min(P1,P2,P3)>0 and C==bM+P1+P2+P3
    return C,P1,P2,P3

def choose(n,k):return comb(n,k) if 0<=k<=n else 0
def coefficient(M,u,v,w):
    return sum(comb(M,t)*choose(M,u+M-t)*choose(2*M-t,v+M-t)*choose(2*M-t,w+M-t) for t in range(M+1))
def vectors():
    z=[]
    for a in range(-3,4):
      for b in range(-3,4):
       for c in range(-3,4):
        if (a,b,c)!=(0,0,0):
            g=gcd(gcd(abs(a),abs(b)),abs(c)); assert g in (1,2,3); z.append((a,b,c,g))
    return z
VECTORS=vectors()
def sgn(x):return (x>0)-(x<0)
def digest(x):return sha256(str(abs(x)).encode()).hexdigest()

def direct_small_check():
    def mul(A,B):
        C=defaultdict(int)
        for u,x in A.items():
          for v,y in B.items():C[tuple(u[i]+v[i] for i in range(3))]+=x*y
        return dict(C)
    one={(0,0,0):1}; x={(0,0,0):1,(1,0,0):1}; y={(0,0,0):1,(0,1,0):1}; z={(0,0,0):1,(0,0,1):1}
    yz=mul(y,z); bracket=dict(yz); bracket[(1,1,1)]=bracket.get((1,1,1),0)+1
    L=one
    for f in (x,y,z,bracket):L=mul(L,f)
    L={(a-1,b-1,c-1):v for (a,b,c),v in L.items()}; power=one; rows=0
    for M in range(7):
        row=binomial_row(M)
        for nu,v in power.items():assert coefficient(M,*nu)==v;rows+=1
        for d in range(1,M+2):
            exact=sum(v for nu,v in power.items() if all(x%d==0 for x in nu))
            assert cyclic_shell(M,d,row)==exact;rows+=1
        power=mul(power,L)
    return rows

def edge_ledger(M,d,e,top=8):
    q,ell=d+1,e+1; sums={1:0,2:0,3:0}; rows=[]
    for a,b,c,g in VECTORS:
        L=coefficient(M,d*a,d*b,d*c); R=coefficient(M,e*a,e*b,e*c); v=ell*L-q*R
        sums[g]+=v; rows.append((v,(a,b,c),g,L,R))
    rows.sort(key=lambda x:x[0]); return sums,rows[:top],list(reversed(rows[-top:]))

def audit_small(b,prime):
    total=Counter(); patterns=Counter(); driver=Counter(); zeros=[]; pzeros=[]; first=None; firstp=None; pairs=ppairs=0
    for M in range(5,SMALL_LIMIT+1):
        ds=list(admissible_scales(M))
        if len(ds)<2:continue
        row=binomial_row(M); data={d:packet_data(M,d,b[M],row) for d in ds}
        for ix,d in enumerate(ds):
          Cd,*Pd=data[d]
          for e in ds[ix+1:]:
            Ce,*Pe=data[e];q,ell=d+1,e+1; center=(e-d)*b[M]
            E=[ell*Pd[k]-q*Pe[k] for k in range(3)]; N=ell*Cd-q*Ce
            assert N==center+sum(E);pairs+=1;total[sgn(N)]+=1;patterns[tuple(sgn(x) for x in E)]+=1
            if N<0:
                driver[min(range(3),key=lambda k:E[k])+1]+=1
                if first is None:first=(M,d,e,N,center,*E)
            if N==0:zeros.append((M,d,e))
            if prime[q] and prime[ell]:
                ppairs+=1
                if N<0 and firstp is None:firstp=(M,q,ell,N)
                if N==0:pzeros.append((M,q,ell))
    assert first and first[:3]==(90,26,27)
    return dict(pairs=pairs,prime_pairs=ppairs,signs=dict(total),patterns=dict(patterns),driver=dict(driver),zeros=zeros,prime_zeros=pzeros,first=first,first_prime=firstp)

def witt(M,d,b):
    r=M-3*d;assert 3<=r<d;q=d+1
    V=[cyclic_shell(r+a*d,d) for a in range(4)];assert V[0]==b[r]
    n1=V[1]-V[0];n2=V[2]-2*V[1]+V[0];n3=V[3]-3*V[2]+3*V[1]-V[0]
    assert n1%q==0 and n2%(q*q)==0 and n3%(q**3)==0
    D1,D2,D3=n1//q,n2//(q*q),n3//(q**3)
    assert V[3]==b[r]+3*q*D1+3*q*q*D2+q**3*D3
    return V[3],D1,D2,D3

def audit_targets(b,prime):
    scales=Ms=pairs=wr=0; signs=Counter(); dg=0; zeros=[]; neg=[]; rows=[]; first=None; minabs=None; pad=Counter(); both=[];both2=[]
    for M in range(5,M_LIMIT+1):
        n=M+3; T=[]
        for d in admissible_scales(M):
            q=d+1;r=M-3*d
            if prime[q] and b[r]%q==0:T.append(d)
        scales+=len(T)
        if len(T)<2:continue
        Ms+=1;row=binomial_row(M);data={d:packet_data(M,d,b[M],row) for d in T}
        for d in T:
            q=d+1;r=M-3*d;C=data[d][0];assert C%q==0
            C0,D1,D2,D3=witt(M,d,b);assert C0==C and C//q==b[r]//q+3*D1+3*q*D2+q*q*D3;wr+=1
        for ix,d in enumerate(T):
          q=d+1;Cd,*Pd=data[d];r=M-3*d;Td=Cd//q
          for e in T[ix+1:]:
            ell=e+1;Ce,*Pe=data[e];s=M-3*e;Te=Ce//ell;h=e-d
            assert h%2==0 and r-s==3*h
            E=[ell*Pd[k]-q*Pe[k] for k in range(3)];center=h*b[M];N=ell*Cd-q*Ce
            assert N==center+sum(E) and N%(q*ell)==0
            D=N//(q*ell);pairs+=1;signs[sgn(D)]+=1;dg=gcd(dg,abs(D))
            rec=(n,M,q,ell,r,s,sgn(D),abs(D).bit_length(),digest(D));rows.append(rec)
            if D==0:zeros.append(rec)
            if D<0:
                neg.append(rec)
                if first is None:first=(n,M,d,e,q,ell,r,s,D,center,*E)
            if minabs is None or abs(D)<minabs[0]:minabs=(abs(D),rec)
            mq=(Td-Te)%q==0;ml=(Td-Te)%ell==0;mq2=(Td-Te)%(q*q)==0;ml2=(Td-Te)%(ell*ell)==0
            pad['mod_q']+=mq;pad['mod_ell']+=ml;pad['both_mod_1']+=mq and ml;pad['mod_q2']+=mq2;pad['mod_ell2']+=ml2;pad['both_mod_2']+=mq2 and ml2
            if mq and ml:both.append(rec)
            if mq2 and ml2:both2.append(rec)
    assert first and first[:8]==(743,740,196,210,197,211,152,110)
    return dict(target_scales=scales,target_Ms=Ms,pairs=pairs,witt_rows=wr,signs=dict(signs),delta_gcd=dg,zeros=zeros,negative=neg,rows=rows,first=first,min_abs=minabs,padic=dict(pad),both=both,both2=both2)

def print_edge(label,M,d,e):
    sums,lo,hi=edge_ledger(M,d,e);print(label,{'M':M,'d':d,'e':e,'q':d+1,'ell':e+1});print(label+'_PACKETS',sums);print(label+'_LOW',lo);print(label+'_HIGH',hi)

def main():
    print('Q3443_STANDALONE');pc=Counter(g for *_,g in VECTORS);print('PACKET_CARDINALITIES',pc);assert pc==Counter({1:290,2:26,3:26})
    print('SMALL_INDEPENDENT_ROWS',direct_small_check());b=apery_values(M_LIMIT);prime=primes_upto(M_LIMIT//3+5)
    S=audit_small(b,prime);print('SMALL_SUMMARY',S);print_edge('FIRST_UNRESTRICTED',90,26,27)
    T=audit_targets(b,prime);print('TARGET_SUMMARY',{k:v for k,v in T.items() if k not in ('rows','negative','first','min_abs')});print('TARGET_MIN_ABS',T['min_abs']);print('TARGET_ROWS',T['rows'])
    f=T['first'];print('FIRST_TARGET',f[:8],'bits',abs(f[8]).bit_length(),'sha256',digest(f[8]));print('FIRST_TARGET_TERMS',f[9:]);print_edge('FIRST_TARGET_EDGE',740,196,210)
    print('ALL_ASSERTIONS_PASSED',True)
if __name__=='__main__':main()
