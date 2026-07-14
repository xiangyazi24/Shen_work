from __future__ import annotations

from pathlib import Path
from mpmath import mp

mp.dps = 360

P_ROW = [mp.mpf(30921), mp.mpf(-32972), mp.mpf(8240)]
Q_ROW = [mp.mpf(33750), mp.mpf(-36000), mp.mpf(9000)]
G = mp.catalan


def MH(k: int):
    n = int(k)
    m11 = (-2*n-5)*(n+3)**2*(136*n**4+1424*n**3+5548*n**2+9551*n+6141)
    m12 = 384*n**6+6384*n**5+44168*n**4+162698*n**3+336377*n**2+369933*n+169011
    m13 = -(480*n**4+4980*n**3+19210*n**2+32690*n+20730)
    m21 = (n+2)**2*(n+3)**2*(4*n+10)*(48*n**3+386*n**2+1017*n+879)
    m22 = (n+2)**2*(-272*n**5-3848*n**4-21732*n**3-61184*n**2-85761*n-47808)
    m23 = (n+2)**2*(320*n**3+2540*n**2+6610*n+5640)
    m31 = (-4*n-10)*(n+2)**2*(n+3)**2*(32*n**4+302*n**3+1037*n**2+1530*n+813)
    m32 = (n+2)**2*(192*n**6+2984*n**5+19116*n**4+64452*n**3+120256*n**2+117279*n+46476)
    m33 = (n+2)**2*(-16*n**5-408*n**4-2912*n**3-8884*n**2-12254*n-6240)
    delta = -2*(n+2)**2*(n+3)**2*(2*n+5)*(2*n+7)**2
    d = mp.mpf(delta)
    return mp.matrix([
        [mp.mpf(m11)/d, mp.mpf(m12)/d, mp.mpf(m13)/d],
        [mp.mpf(m21)/d, mp.mpf(m22)/d, mp.mpf(m23)/d],
        [mp.mpf(m31)/d, mp.mpf(m32)/d, mp.mpf(m33)/d],
    ])


def maxabs_vec(v):
    return max(abs(v[i]) for i in range(v.rows))


def dot(row, v):
    return sum(row[i]*v[i] for i in range(3))


def normalize_first(v):
    if abs(v[0]) < mp.mpf('1e-300'):
        raise ArithmeticError('first coordinate too small for normalization')
    return v / v[0]


def normalize_unit(v):
    nr = mp.sqrt(sum(abs(v[i])**2 for i in range(3)))
    w = v / nr
    if dot(Q_ROW, w) < 0:
        w = -w
    return w


def backward_projective(N: int, seed_index: int = 0, use_transpose: bool = False):
    v = mp.matrix(3, 1)
    v[seed_index] = 1
    for n in range(N-1, -1, -1):
        A = MH(n)
        if use_transpose:
            A = A.T
        v = A * v
        s = maxabs_vec(v)
        if s == 0:
            raise ArithmeticError('zero vector')
        v /= s
    return normalize_first(v)


def direct_row_ratios(N: int):
    rp = mp.matrix([P_ROW])
    rq = mp.matrix([Q_ROW])
    for n in range(N):
        A = MH(n)
        rp = rp * A
        rq = rq * A
        s = max(max(abs(rp[0,j]) for j in range(3)),
                max(abs(rq[0,j]) for j in range(3)))
        rp /= s
        rq /= s
    return [rp[0,j]/rq[0,j] for j in range(3)]


def digits_agree(x, y):
    den = max(mp.mpf(1), abs(x), abs(y))
    e = abs(x-y)/den
    if e == 0:
        return mp.inf
    return -mp.log10(e)


def pslq_rel(vals, maxcoeff=10**12, tol_exp=190, maxsteps=10000):
    vals = [mp.mpf(x) for x in vals]
    tol = mp.mpf(10) ** (-tol_exp)
    try:
        return mp.pslq(vals, tol=tol, maxcoeff=maxcoeff, maxsteps=maxsteps)
    except Exception as exc1:
        try:
            from mpmath.identification import pslq
            return pslq(mp, vals, tol=tol, maxcoeff=maxcoeff, maxsteps=maxsteps)
        except Exception as exc2:
            return f'PSLQ error: {type(exc1).__name__}: {exc1}; fallback: {type(exc2).__name__}: {exc2}'


def fmt(x, digits=225):
    return mp.nstr(x, digits)


# Projective convergence in the convention relevant to x_0 M(0)...M(N-1)e_1.
Ns = [80, 100, 120, 140, 160, 180, 200, 220]
Vs = {N: backward_projective(N, 0, False) for N in Ns}
V = Vs[220]
V_unit = normalize_unit(V)

# Seed independence.
V_seed = [backward_projective(220, j, False) for j in range(3)]

# Convention audit: incorrectly transposed backward transport.
V_T = backward_projective(220, 0, True)

pV = dot(P_ROW, V)
qV = dot(Q_ROW, V)
ratio = pV/qV
residual = pV - G*qV

pVu = dot(P_ROW, V_unit)
qVu = dot(Q_ROW, V_unit)
ratio_u = pVu/qVu

# Direct product ratios for all three output columns.
direct = {N: direct_row_ratios(N) for N in [80, 120, 160, 200]}

# PSLQ tests.  The first relation should be [1,-1].
rel_ratio = pslq_rel([pV, G*qV], maxcoeff=10**6, tol_exp=190)
rel_requested = pslq_rel([pV, qV, G*qV-pV], maxcoeff=10**6, tol_exp=190)

sqrt2 = mp.sqrt(2)
pi = mp.pi
log2 = mp.log(2)
zeta3 = mp.zeta(3)
Khalf = mp.ellipk(mp.mpf('0.5'))
Ksilver = mp.ellipk((sqrt2-1)**2)
Kminus1 = mp.ellipk(-1)

basis_names = ['1','G','pi','log(2)','pi^2','G^2','pi*G','pi*log(2)','G*log(2)','zeta(3)','K(1/2)','K((sqrt2-1)^2)','K(-1)']
basis_vals = [1,G,pi,log2,pi**2,G**2,pi*G,pi*log2,G*log2,zeta3,Khalf,Ksilver,Kminus1]
rel_q_small = pslq_rel([qV] + basis_vals, maxcoeff=10**12, tol_exp=180, maxsteps=30000)
rel_p_small = pslq_rel([pV] + basis_vals, maxcoeff=10**12, tol_exp=180, maxsteps=30000)
rel_v1 = pslq_rel([V[1]] + basis_vals, maxcoeff=10**12, tol_exp=180, maxsteps=30000)
rel_v2 = pslq_rel([V[2]] + basis_vals, maxcoeff=10**12, tol_exp=180, maxsteps=30000)

# Smaller, more robust pairwise/triple searches.
small_tests = {}
for label, x in [('qV',qV),('pV',pV),('V1',V[1]),('V2',V[2])]:
    small_tests[label] = {
        'alg_sqrt2': pslq_rel([x,1,sqrt2], maxcoeff=10**20, tol_exp=190),
        'G_pi_log2': pslq_rel([x,1,G,pi,log2], maxcoeff=10**20, tol_exp=190),
        'elliptic': pslq_rel([x,1,Khalf,Ksilver,Kminus1,pi], maxcoeff=10**20, tol_exp=190),
    }

lines = []
lines.append('# Q4913 high-precision Birkhoff coefficient-vector computation')
lines.append('')
lines.append('Working precision: 360 decimal digits.')
lines.append('Normalization A: V[0]=1. Normalization B: Euclidean norm 1 and q·V>0.')
lines.append('')
lines.append('## Projective stability')
for a,b in zip(Ns[:-1],Ns[1:]):
    ds = min(digits_agree(Vs[a][j], Vs[b][j]) for j in range(3))
    lines.append(f'- N={a} versus N={b}: minimum coordinate agreement = {fmt(ds,30)} decimal digits')
lines.append('')
lines.append('Seed checks at N=220 (all normalized by first coordinate):')
for j,w in enumerate(V_seed):
    ds = min(digits_agree(V[jj], w[jj]) for jj in range(3))
    lines.append(f'- seed e_{j+1}: minimum agreement with e_1 seed = {fmt(ds,30)} digits')
lines.append('')
lines.append('## V with V[0]=1')
for i in range(3):
    lines.append(f'V[{i}] = {fmt(V[i])}')
lines.append('')
lines.append('p·V = ' + fmt(pV))
lines.append('q·V = ' + fmt(qV))
lines.append('(p·V)/(q·V) = ' + fmt(ratio))
lines.append('Catalan G = ' + fmt(G))
lines.append('ratio - G = ' + fmt(ratio-G))
lines.append('p·V - G q·V = ' + fmt(residual))
lines.append('')
lines.append('## Unit-norm normalization')
for i in range(3):
    lines.append(f'V_unit[{i}] = {fmt(V_unit[i])}')
lines.append('p·V_unit = ' + fmt(pVu))
lines.append('q·V_unit = ' + fmt(qVu))
lines.append('ratio_unit - G = ' + fmt(ratio_u-G))
lines.append('')
lines.append('## Direct row-product audit')
for N,rs in direct.items():
    lines.append(f'N={N}:')
    for j,r in enumerate(rs):
        lines.append(f'  column {j}: ratio-G = {fmt(r-G,80)}')
lines.append('')
lines.append('## Transpose-convention audit')
lines.append('V_T (backward M(n)^T, normalized first coordinate) =')
for i in range(3):
    lines.append(f'  {fmt(V_T[i],100)}')
lines.append('transpose ratio - G = ' + fmt(dot(P_ROW,V_T)/dot(Q_ROW,V_T)-G,100))
lines.append('')
lines.append('## PSLQ')
lines.append('PSLQ[p·V, G q·V] = ' + repr(rel_ratio))
lines.append('PSLQ[p·V, q·V, G q·V-p·V] = ' + repr(rel_requested))
lines.append('Broad basis order: ' + ', '.join(basis_names))
lines.append('PSLQ[q·V, basis] = ' + repr(rel_q_small))
lines.append('PSLQ[p·V, basis] = ' + repr(rel_p_small))
lines.append('PSLQ[V[1], basis] = ' + repr(rel_v1))
lines.append('PSLQ[V[2], basis] = ' + repr(rel_v2))
for label, tests in small_tests.items():
    lines.append(label + ': ' + repr(tests))
lines.append('')
lines.append('## Constants used in elliptic tests')
lines.append('K(1/2) = ' + fmt(Khalf,100))
lines.append('K((sqrt(2)-1)^2) = ' + fmt(Ksilver,100))
lines.append('K(-1) = ' + fmt(Kminus1,100))

out = Path('tmp/q4913_result.md')
out.write_text('\n'.join(lines) + '\n', encoding='utf-8')
print('\n'.join(lines[:80]))
