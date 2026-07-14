from sage.all import *

print('Q4892 exact Delannoy single-sum search')
NMAX=70
TRAIN=50

# ------------------------------------------------------------
# Exact CMF and H-normalized first denominator column.
# ------------------------------------------------------------
def M(x):
    P=x.parent()
    return matrix(P,[
      [(-2*x-5)*(x+3)^2*(136*x^4+1424*x^3+5548*x^2+9551*x+6141),
       384*x^6+6384*x^5+44168*x^4+162698*x^3+336377*x^2+369933*x+169011,
       -480*x^4-4980*x^3-19210*x^2-32690*x-20730],
      [(x+2)^2*(x+3)^2*(4*x+10)*(48*x^3+386*x^2+1017*x+879),
       (x+2)^2*(-272*x^5-3848*x^4-21732*x^3-61184*x^2-85761*x-47808),
       (x+2)^2*(320*x^3+2540*x^2+6610*x+5640)],
      [(-4*x-10)*(x+2)^2*(x+3)^2*(32*x^4+302*x^3+1037*x^2+1530*x+813),
       (x+2)^2*(192*x^6+2984*x^5+19116*x^4+64452*x^3+120256*x^2+117279*x+46476),
       (x+2)^2*(-16*x^5-408*x^4-2912*x^3-8884*x^2-12254*x-6240)]])

def delta(x):
    return -2*(x+2)^2*(x+3)^2*(2*x+5)*(2*x+7)^2

def qhat_values(N):
    q=vector(QQ,[33750,-36000,9000]); out=[]
    for n in range(N+1):
        out.append(q[0])
        if n<N: q=q*(M(QQ(n))/delta(QQ(n)))
    return out

QH=qhat_values(NMAX)
assert QH[0]==33750 and QH[1]==QQ(5295375,4)
print('\nFIRST 20 Qhat_n')
for n in range(20):
    print('%2d | %s | %s' % (n,QH[n],RealField(45)(QH[n])))

# ------------------------------------------------------------
# Delannoy-square summand and harmonic tables.
# ------------------------------------------------------------
def FD(n,k):
    if k<0 or k>n: return ZZ(0)
    return 2^k*binomial(2*k,k)*binomial(n,k)*binomial(n+k,k)

L=2*NMAX+5
H=[QQ(0)]*L; H2=[QQ(0)]*L; O=[QQ(0)]*L; O2=[QQ(0)]*L; C=[QQ(0)]*L
for m in range(1,L):
    H[m]=H[m-1]+QQ(1,m); H2[m]=H2[m-1]+QQ(1,m^2)
    O[m]=O[m-1]+QQ(1,2*m-1); O2[m]=O2[m-1]+QQ(1,(2*m-1)^2)
    C[m]=C[m-1]+QQ((-1)^(m-1),(2*m-1)^2)

# Unique k-only inverse transform.
W=[]
for n in range(NMAX+1):
    W.append((QH[n]-sum(FD(n,k)*W[k] for k in range(n)))/FD(n,n))
print('\nUNIQUE k-ONLY WEIGHTS')
for k in range(20):
    rat='-' if k==19 or W[k]==0 else W[k+1]/W[k]
    print('%2d | %s | ratio=%s' % (k,W[k],rat))

# ------------------------------------------------------------
# Exact fitting helpers.
# ------------------------------------------------------------
PRIMES=[1000003,1000033,1000037]
def mod_matrix(A,p):
    F=GF(p)
    return matrix(F,A.nrows(),A.ncols(),[F(x) for x in A.list()])

def fit(columns,target,train=TRAIN,verify=NMAX):
    A=matrix(QQ,train+1,len(columns),lambda i,j: columns[j][i])
    b=vector(QQ,target[:train+1])
    for p in PRIMES:
        Ap=mod_matrix(A,p); bp=vector(GF(p),[GF(p)(x) for x in b])
        if Ap.rank()!=Ap.augment(matrix(GF(p),len(bp),1,list(bp))).rank():
            return None,'inconsistent mod %s'%p
    if A.rank()!=A.augment(matrix(QQ,len(b),1,list(b))).rank():
        return None,'inconsistent over QQ'
    sol=A.solve_right(b)
    for n in range(verify+1):
        if sum(sol[j]*columns[j][n] for j in range(len(columns)))!=target[n]:
            return None,'verification failure n=%s'%n
    return sol,None

def monomials(d): return [(a,b) for a in range(d+1) for b in range(d+1-a)]

features={
 '1':lambda n,k:QQ(1), 'Hk':lambda n,k:H[k], 'Hk2':lambda n,k:H2[k],
 'Ok':lambda n,k:O[k], 'Ok2':lambda n,k:O2[k], 'Ok_sq':lambda n,k:O[k]^2,
 'Ck':lambda n,k:C[k], 'dO':lambda n,k:O[n+k]-O[k],
 'dO2':lambda n,k:O2[n+k]-O2[k], 'dO_sq':lambda n,k:(O[n+k]-O[k])^2,
 'dH':lambda n,k:H[n+k]-H[k], 'dH2':lambda n,k:H2[n+k]-H2[k],
 'Hsym':lambda n,k:H[n+k]+H[n-k]-2*H[n],
 'H2sym':lambda n,k:H2[n+k]+H2[n-k]-2*H2[n],
 'dC':lambda n,k:C[n+k]-C[k]
}
dens={
 '1':lambda n,k:QQ(1), '2k+1':lambda n,k:QQ(2*k+1),
 '(2k+1)^2':lambda n,k:QQ((2*k+1)^2), 'n+k+1':lambda n,k:QQ(n+k+1),
 '2n+2k+1':lambda n,k:QQ(2*n+2*k+1), 'n-k+1':lambda n,k:QQ(n-k+1),
 'edgeprod':lambda n,k:QQ((n-k+1)*(n+k+1)), 'n+1':lambda n,k:QQ(n+1)
}
cache={}
def col(fname,a,b,dname):
    key=(fname,a,b,dname)
    if key in cache: return cache[key]
    f=features[fname]; den=dens[dname]; out=[]
    for n in range(NMAX+1):
        out.append(sum(FD(n,k)*n^a*k^b*f(n,k)/den(n,k) for k in range(n+1)))
    cache[key]=out; return out

def search(label,names,d,dname):
    labs=[]; cols=[]
    for name in names:
        for a,b in monomials(d): labs.append((name,a,b,dname)); cols.append(col(name,a,b,dname))
    if len(cols)>TRAIN+1:
        print('SKIP',label,'columns',len(cols)); return None
    sol,why=fit(cols,QH)
    if sol is None:
        print('NO',label,why); return None
    nz=[(labs[j],sol[j]) for j in range(len(sol)) if sol[j]]
    print('FOUND',label,'nonzero terms',len(nz))
    for t,c in nz: print(' ',c,'*',t)
    return nz

# k-only recognition in elementary harmonic bases.
print('\nK-ONLY WEIGHT RECOGNITION')
kfeatures={'1':lambda k:QQ(1),'Hk':lambda k:H[k],'Hk2':lambda k:H2[k],
           'Ok':lambda k:O[k],'Ok2':lambda k:O2[k],'Ok_sq':lambda k:O[k]^2,
           'Ck':lambda k:C[k]}
for names in [('1',),('1','Hk'),('1','Ok'),('1','Ok','Ok2','Ok_sq'),
              ('1','Ck'),('1','Hk','Hk2','Ok','Ok2','Ck')]:
    got=False
    for d in range(7):
        labs=[(nm,a) for nm in names for a in range(d+1)]
        cols=[[k^a*kfeatures[nm](k) for k in range(31)] for nm,a in labs]
        sol,why=fit(cols,W[:31],20,30)
        if sol is not None:
            print('FOUND w_k',names,'degree',d,[(labs[j],sol[j]) for j in range(len(sol)) if sol[j]])
            got=True; break
    if not got: print('NO w_k',names,'through degree 6')

FOUND=None
print('\nPOLYNOMIAL R(n,k)')
for d in range(10):
    FOUND=search('polynomial total degree <=%s'%d,('1',),d,'1')
    if FOUND: break

if FOUND is None:
    print('\nSIMPLE RATIONAL DENOMINATORS')
    for dn in ['2k+1','(2k+1)^2','n+k+1','2n+2k+1','n-k+1','edgeprod','n+1']:
        for d in range(8):
            FOUND=search('P/%s degree<=%s'%(dn,d),('1',),d,dn)
            if FOUND: break
        if FOUND: break

if FOUND is None:
    print('\nHARMONIC AND PARAMETER-DERIVATIVE FEATURES')
    groups=[('1','Hk'),('1','Hk','Hk2'),('1','Ok'),('1','Ok','Ok2','Ok_sq'),
            ('1','dO'),('1','dO','dO2','dO_sq'),('1','dH','dH2'),
            ('1','Hsym','H2sym'),('1','Ck'),('1','Ck','Ok'),('1','Ck','dO'),('1','dC')]
    for names in groups:
        maxd=3 if len(names)<=3 else 2
        for dn in ['1','2k+1']:
            for d in range(maxd+1):
                FOUND=search('%s / %s degree<=%s'%(names,dn,d),names,d,dn)
                if FOUND: break
            if FOUND: break
        if FOUND: break

print('\nFINAL')
if FOUND:
    print('EXACT SINGLE-SUM FORMULA FOUND; verified through n=%s.'%NMAX)
else:
    print('NO FORMULA IN THE DISPLAYED FINITE SEARCH LADDER.')
    print('Excluded exactly: polynomial total degree <=9; each listed simple denominator')
    print('with numerator degree <=7; and the displayed harmonic/odd-harmonic/Jacobi')
    print('parameter-derivative/Catalan-tail feature groups with the printed degree bounds.')
