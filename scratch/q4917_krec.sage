from sage.all import *

# Q4917: discover a common polynomial-coefficient recurrence for the
# Delannoy-basis coefficients f(k), g(k) of the H-normalized CMF rows.

NTERMS = 260
PRIMES = [1000003, 1000033, 1000037]
MAX_ORDER = 24
MAX_DEGREE = 36


def M_entries(n, R):
    n = R(n)
    m11 = (-2*n-5)*(n+3)^2*(136*n^4+1424*n^3+5548*n^2+9551*n+6141)
    m12 = 384*n^6+6384*n^5+44168*n^4+162698*n^3+336377*n^2+369933*n+169011
    m13 = -480*n^4-4980*n^3-19210*n^2-32690*n-20730
    m21 = (n+2)^2*(n+3)^2*(4*n+10)*(48*n^3+386*n^2+1017*n+879)
    m22 = (n+2)^2*(-272*n^5-3848*n^4-21732*n^3-61184*n^2-85761*n-47808)
    m23 = (n+2)^2*(320*n^3+2540*n^2+6610*n+5640)
    m31 = (-4*n-10)*(n+2)^2*(n+3)^2*(32*n^4+302*n^3+1037*n^2+1530*n+813)
    m32 = (n+2)^2*(192*n^6+2984*n^5+19116*n^4+64452*n^3+120256*n^2+117279*n+46476)
    m33 = (n+2)^2*(-16*n^5-408*n^4-2912*n^3-8884*n^2-12254*n-6240)
    return matrix(R, [[m11,m12,m13],[m21,m22,m23],[m31,m32,m33]])


def delta_H(n, R):
    n = R(n)
    return -2*(n+2)^2*(n+3)^2*(2*n+5)*(2*n+7)^2


def cmf_sequences_mod(p, N):
    F = GF(p)
    q = vector(F, [33750,-36000,9000])
    pp = vector(F, [30921,-32972,8240])
    Q = []
    P = []
    for n in range(N):
        Q.append(q[0]); P.append(pp[0])
        MH = M_entries(n,F) / delta_H(n,F)
        q = q*MH
        pp = pp*MH
    return Q,P


def B_mod(n,k,F):
    return F(2)^k * F(binomial(2*k,k)) * F(binomial(n,k)) * F(binomial(n+k,k))


def invert_delannoy(seq,F):
    out=[]
    for n in range(len(seq)):
        s=seq[n]
        for k in range(n):
            s -= B_mod(n,k,F)*out[k]
        diag=B_mod(n,n,F)
        if diag==0:
            raise ZeroDivisionError('Delannoy diagonal vanished at n=%s'%n)
        out.append(s/diag)
    return out


def recurrence_matrix(seqs,r,d,F,train_end):
    rows=[]
    # equations n=0,...,train_end-1
    for seq in seqs:
        for n in range(train_end):
            row=[]
            nn=F(n)
            powers=[F(1)]
            for m in range(1,d+1): powers.append(powers[-1]*nn)
            for j in range(r+1):
                row.extend([seq[n+j]*powers[m] for m in range(d+1)])
            rows.append(row)
    return matrix(F,rows)


def verify_vector(v,seqs,r,d,F,start,end):
    for seq in seqs:
        for n in range(start,end):
            total=F(0)
            pos=0
            nn=F(n)
            powers=[F(1)]
            for m in range(1,d+1): powers.append(powers[-1]*nn)
            for j in range(r+1):
                for m in range(d+1):
                    total += v[pos]*powers[m]*seq[n+j]
                    pos += 1
            if total != 0:
                return False,(n,total)
    return True,None


def normalize_vec(v):
    # Normalize at the last nonzero coefficient.
    for a in reversed(v):
        if a:
            return vector(v.base_ring(),[x/a for x in v])
    return v


def poly_list(v,r,d,F):
    R.<k> = PolynomialRing(F)
    ans=[]
    pos=0
    for j in range(r+1):
        p=R(0)
        for m in range(d+1):
            p += v[pos]*k^m; pos += 1
        ans.append(p)
    return ans


def search_one_prime(p):
    print('\n=== prime',p,'===',flush=True)
    F=GF(p)
    Q,P=cmf_sequences_mod(p,NTERMS)
    f=invert_delannoy(Q,F)
    g=invert_delannoy(P,F)
    print('first f:',f[:8])
    print('first g:',g[:8])

    # Search minimal order first, then degree. Use both f and g simultaneously.
    for r in range(1,MAX_ORDER+1):
        for d in range(0,MAX_DEGREE+1):
            U=(r+1)*(d+1)
            available=NTERMS-r
            train=min(available-30, max(U+8, 40))
            if train<=0 or 2*train < U:
                continue
            A=recurrence_matrix([f,g],r,d,F,train)
            ker=A.right_kernel()
            if ker.dimension()==0:
                continue
            print('kernel hit order=%d degree=%d dim=%d rank=%d cols=%d train=%d' %
                  (r,d,ker.dimension(),A.rank(),A.ncols(),train),flush=True)
            for basisv in ker.basis():
                v=normalize_vec(basisv)
                ok,why=verify_vector(v,[f,g],r,d,F,train,available)
                if ok:
                    pols=poly_list(v,r,d,F)
                    print('VERIFIED CANDIDATE order=%d degree=%d' % (r,d),flush=True)
                    for j,pol in enumerate(pols):
                        print('p%d ='%j,pol)
                        print('factor(p%d) ='%j,factor(pol))
                    return r,d,pols
                else:
                    print('spurious basis vector',why)
    print('NO CANDIDATE IN SEARCH BOX')
    return None


results=[]
for p in PRIMES:
    results.append(search_one_prime(p))
print('\nSUMMARY:',[(None if x is None else (x[0],x[1])) for x in results])
