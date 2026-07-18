ANSWER Q50 de3dfd1b

# Executing the dyadic/large-sieve program for the Apéry pair variance

## Executive verdict

The program produces several exact identities and one useful unconditional local theorem, but it does **not** yet prove

\[
V_2(p)=O(p^2).
\]

The failure is sharply localized.

1. **Every cross-kernel does have a continuant formula.** With the sign conventions in the question,
   \[
   K(r,s)=a_rb_s-b_ra_s
   =-6\,
   \frac{N_{s-r}(r)}{\prod_{j=r+1}^{s}j^3}
   \qquad(0\le r<s\le p-1).
   \]
   The four terms of \(\Pi_{h,k}\) are therefore explicit continuants after splitting into finitely many order chambers.

2. **Short chord gaps do not make the mixed certificate low-degree.** In the chamber
   \[
   x<x+h<y<y+k,
   \]
   put \(d=y-x\). After clearing denominators, the degree is controlled by the total span \(d+k\), not by \(h+k\). The mixed bridge \(y-x\) is the source of the full complexity.

3. **A genuine local theorem is available.** If the two gaps and the bridge length are all at most \(R\), then a nondegenerate degree argument gives \(O(R^4)\) parallel-secant configurations. Hence the part in which all four endpoints lie in a window of length \(O(p^{1/2})\) is \(O(p^2)\). Without a uniform nondegeneracy/content lemma, the unconditional trivial threshold is only \(R\le p^{1/3}\).

4. **The proposed two-variable Lang--Weil step does not apply globally.** Even under the optimistic but false premise that the fixed-\((h,k)\) curve had degree \(O(h+k)\) and one nonforced absolutely irreducible component, summing individual Hasse--Weil errors would reach only
   \[
   h,k\le p^{3/8},
   \]
   not \(p^{1/2}\).

5. **Plücker gives an exact two-channel dyadic recursion.** For every split point \(z\),
   \[
   K(r,s)
   =
   \frac{K(r,z+1)K(z,s)-K(r,z)K(z+1,s)}{K(z,z+1)}.
   \]
   This halves long spans while preserving rank two. It is the correct cocycle, but it is an identity rather than an estimate: it does not supply mixing for the prescribed deterministic products.

6. **The precise large-sieve target is now clear.** If
   \[
   f_h(\xi)=P_{h,\xi}-\frac{M_h}{p+1},
   \]
   then the robust theorem needed is
   \[
   \sum_{\xi\in\mathbf P^1(\mathbf F_p)}
   \left|\sum_h c_hf_h(\xi)\right|^2
   \ll p\sum_h|c_h|^2.
   \tag{LS}
   \]
   Taking \(c_h=1\) proves \(V_2(p)\ll p^2\).

7. **There is an additional prerequisite.** The current repository proves the forced palindromic state returns, but the assertion that they are the only universal pairs remains computational. One separately needs
   \[
   U_p=\#\{\{r,s\}:Q_r=Q_s\}=O(p).
   \tag{U}
   \]
   Pair variance plus (U) closes the projection-energy theorem; pair variance alone does not control the universal term \(2U_p\).

Thus the endgame has two load-bearing statements:

\[
\boxed{
U_p\ll p
\quad\text{and}\quad
\text{dyadic projective large sieve (LS).}
}
\]

The continuant degree theory proves a meaningful local piece and supplies the exact two-channel recursion, but the missing theorem is still an **average cross-base mixing estimate**.

---

# 1. Exact pair-variance identity

Let

\[
Q_n=(a_n,b_n)\in\mathbf F_p^2,
\qquad n\in\mathbf Z/p\mathbf Z,
\]

and use the palindromy

\[
Q_{-1-n}=Q_n.
\]

Put

\[
\mathcal H=\left\{1,\ldots,\frac{p-1}{2}\right\}.
\]

Every unordered pair of distinct indices has a unique representation

\[
\{x,x+h\},
\qquad x\in\mathbf F_p,\quad h\in\mathcal H.
\]

For \(h\in\mathcal H\), define the chord

\[
\Delta_h(x)=Q_{x+h}-Q_x.
\]

Let

\[
\mathcal R_h=\{x:\Delta_h(x)=0\},
\qquad r_h=|\mathcal R_h|,
\]

and

\[
\mathcal X_h=\mathbf F_p\setminus\mathcal R_h,
\qquad M_h=|\mathcal X_h|=p-r_h.
\]

For a nonzero chord define its normal direction

\[
\Theta_h(x)
=
[b_{x+h}-b_x:-(a_{x+h}-a_x)]
\in\mathbf P^1(\mathbf F_p).
\]

For \(\xi\in\mathbf P^1(\mathbf F_p)\), set

\[
P_{h,\xi}
=\#\{x\in\mathcal X_h:\Theta_h(x)=\xi\},
\]

and

\[
P_\xi=\sum_{h\in\mathcal H}P_{h,\xi}.
\]

The number of universal unordered pairs is

\[
U_p=\sum_{h\in\mathcal H}r_h.
\tag{1.1}
\]

Indeed, every unordered index pair has exactly one \((x,h)\) representation. Consequently

\[
M:=\sum_hM_h
=\binom p2-U_p.
\tag{1.2}
\]

The exact mean is therefore

\[
\boxed{
\mu_2=\frac{M}{p+1}
=\frac{\binom p2-U_p}{p+1}.
}
\tag{1.3}
\]

The frequently used formula

\[
\mu_2=\frac{(p-1)^2}{2(p+1)}
\]

requires the additional statement

\[
U_p=\frac{p-1}{2},
\]

i.e. that the palindromic pairs are the only universal pairs. That equality is currently verified but not proved in the repository. For the theorem below, \(U_p=O(p)\) is enough.

## 1.1 Projection energy

For a direction \(\xi\), let

\[
\nu_\xi(c)=\#\{n:\xi\cdot Q_n=c\}.
\]

Then

\[
E_\xi=\sum_c\nu_\xi(c)^2
=p+2U_p+2P_\xi.
\tag{1.4}
\]

Thus

\[
\max_\xi E_\xi
\le
p+2U_p+2\mu_2+2\sqrt{V_2(p)}.
\tag{1.5}
\]

Therefore

\[
U_p=O(p),\qquad V_2(p)=O(p^2)
\]

imply

\[
\sup_\xi E_\xi=O(p).
\]

This is the exact audited form of the pair-variance criterion.

## 1.2 Parallel-secant counts

Define

\[
C_{h,k}
=
\#\{(x,y)\in\mathcal X_h\times\mathcal X_k:
\Theta_h(x)=\Theta_k(y)\}.
\tag{1.6}
\]

Then

\[
C_{h,k}=\sum_\xi P_{h,\xi}P_{k,\xi}.
\]

It follows that

\[
\boxed{
V_2(p)
=
\sum_{h,k\in\mathcal H}
\left(
C_{h,k}-\frac{M_hM_k}{p+1}
\right).
}
\tag{1.7}
\]

This confirms the proposed main term:

\[
\sum_{h,k}\frac{M_hM_k}{p+1}
=
\frac{M^2}{p+1}.
\]

## 1.3 The determinant certificate and state-return correction

Put

\[
K(r,s)=\det(Q_r,Q_s)=a_rb_s-b_ra_s.
\]

Then

\[
\begin{aligned}
\Pi_{h,k}(x,y)
&=\det(\Delta_h(x),\Delta_k(y))\\
&=K(x+h,y+k)-K(x+h,y)\\
&\qquad-K(x,y+k)+K(x,y).
\end{aligned}
\tag{1.8}
\]

For nonzero chords,

\[
\Theta_h(x)=\Theta_k(y)
\iff
\Pi_{h,k}(x,y)=0.
\]

Let

\[
\widetilde C_{h,k}
=
\#\{(x,y)\in\mathbf F_p^2:\Pi_{h,k}(x,y)=0\}.
\]

If either chord is zero, the determinant vanishes automatically. Inclusion--exclusion gives the exact correction

\[
\boxed{
C_{h,k}
=
\widetilde C_{h,k}
-pr_h-pr_k+r_hr_k.
}
\tag{1.9}
\]

This is the complete state-return correction.

## 1.4 Forced palindromic pairs inside \(C_{h,h}\)

Define

\[
\iota_h(x)=-1-h-x.
\]

Palindromy gives

\[
\Delta_h(\iota_h(x))=-\Delta_h(x),
\]

hence

\[
\Theta_h(\iota_h(x))=\Theta_h(x).
\]

A fixed point of \(\iota_h\) satisfies

\[
2x+h+1=0,
\]

so its two endpoints are palindromic and its chord is zero. Thus \(\iota_h\) acts freely on \(\mathcal X_h\).

Consequently \(C_{h,h}\) contains two disjoint forced ordered families:

- \(y=x\);
- \(y=\iota_h(x)\).

Each has size \(M_h\). Therefore

\[
\boxed{
C_{h,h}=2M_h+G_h,
\qquad G_h\ge0,
}
\tag{1.10}
\]

where \(G_h\) counts coincidences between distinct palindromic chord orbits.

The variance can be written as

\[
\boxed{
\begin{aligned}
V_2(p)
={}&
\sum_{h\ne k}
\left(C_{h,k}-\frac{M_hM_k}{p+1}\right)\\
&+\sum_h
\left(2M_h+G_h-\frac{M_h^2}{p+1}\right).
\end{aligned}
}
\tag{1.11}
\]

The diagonal and reflected contributions already have size \(O(p^2)\); they are part of the observed constant near \(2p^2\), not an error to be eliminated.

---

# 2. The general continuant formula for \(K(r,s)\)

The recurrence is

\[
(n+1)^3u_{n+1}=P(n)u_n-n^3u_{n-1},
\]

where

\[
P(n)=(2n+1)(17n^2+17n+5).
\]

Define the continuants

\[
N_0(x)=0,\qquad N_1(x)=1,
\]

and

\[
N_{j+1}(x)
=P(x+j)N_j(x)-(x+j)^6N_{j-1}(x).
\tag{2.1}
\]

Also put

\[
Q_j(x)=\prod_{r=2}^{j}(x+r)^3,
\qquad Q_1(x)=1.
\]

Then

\[
\deg N_j=3(j-1).
\]

For every solution \(u\),

\[
u_{x+j}
=
\frac{N_j(x)}{Q_j(x)}u_{x+1}
-
\frac{(x+1)^3N_{j-1}(x+1)}{Q_j(x)}u_x.
\tag{2.2}
\]

The Wronskian convention in the question is

\[
W_x=a_{x+1}b_x-a_xb_{x+1}
=\frac6{(x+1)^3}.
\]

Since

\[
K(x,x+1)=-W_x,
\]

formula (2.2) gives

\[
\boxed{
K(x,x+j)
=-\frac6{(x+1)^3}\frac{N_j(x)}{Q_j(x)}.
}
\tag{2.3}
\]

Equivalently, for \(0\le r<s\le p-1\),

\[
\boxed{
K(r,s)
=-6\,
\frac{N_{s-r}(r)}{\displaystyle\prod_{t=r+1}^{s}t^3}.
}
\tag{2.4}
\]

For \(r>s\), use antisymmetry

\[
K(r,s)=-K(s,r).
\]

Thus the answer to the first audit question is **yes**: every term in \(\Pi_{h,k}\) has a continuant formula. If the cyclic indexing wraps around \(p\), split into finitely many linear order chambers and apply (2.4) after antisymmetry.

---

# 3. An explicit cleared formula in one order chamber

Consider the chamber

\[
0\le x<x+h<y<y+k\le p-1,
\]

and put

\[
d=y-x>h.
\]

Define

\[
A_h(x)=\prod_{i=1}^{h}(x+i)^3,
\]

and

\[
B_k(y)=\prod_{j=1}^{k}(y+j)^3.
\]

Let

\[
D(x,y+k)=\prod_{t=x+1}^{y+k}t^3.
\]

Multiplying (1.8) by the common denominator and using (2.4) gives

\[
D(x,y+k)\Pi_{h,k}(x,y)
=-6\,\mathscr P_{h,k,d}(x),
\tag{3.1}
\]

where

\[
\boxed{
\begin{aligned}
\mathscr P_{h,k,d}(x)
={}&A_h(x)N_{d+k-h}(x+h)\\
&-A_h(x)B_k(x+d)N_{d-h}(x+h)\\
&-N_{d+k}(x)\\
&+B_k(x+d)N_d(x).
\end{aligned}
}
\tag{3.2}
\]

Every term has degree at most

\[
3(d+k-1).
\]

Indeed,

\[
\begin{aligned}
\deg(A_hN_{d+k-h})&=3h+3(d+k-h-1),\\
\deg(A_hB_kN_{d-h})&=3h+3k+3(d-h-1),\\
\deg N_{d+k}&=3(d+k-1),\\
\deg(B_kN_d)&=3k+3(d-1).
\end{aligned}
\]

They are all equal to \(3(d+k-1)\) before any cancellation.

This formula identifies the central obstruction:

\[
\boxed{
\text{the degree is controlled by the total span }d+k,
\text{ not by the chord gaps }h+k.
}
\]

The other endpoint orderings have analogous formulas; their degree is bounded by a constant times the diameter of the union of the two chords.

Therefore the proposed statement

> “for \(h\sim H\), \(k\sim K\), the bivariate certificate has degree \(O(H+K)\)”

is false unless the base separation is localized as well.

---

# 4. What the degree method actually proves

## 4.1 Dyadic bridge localization

Fix dyadic ranges

\[
h\asymp H,\qquad k\asymp K,\qquad d\asymp D,
\]

inside one order chamber. Assume first that the cleared polynomial is not identically zero modulo \(p\) after the forced diagonal/reflection cases have been removed.

For fixed \((h,k,d)\), (3.2) gives

\[
\#\{x:\mathscr P_{h,k,d}(x)=0\}
\ll
\min\{p,H+K+D\}.
\tag{4.1}
\]

There are \(O(HKD)\) choices of \((h,k,d)\), so

\[
\boxed{
\mathcal N(H,K,D)
\ll
HKD\min\{p,H+K+D\}.
}
\tag{4.2}
\]

This is the exact degree-only dyadic bound.

If

\[
H,K,D\le R\le p,
\]

then

\[
\mathcal N(H,K,D)\ll R^4.
\tag{4.3}
\]

Summing all blocks with total endpoint diameter at most \(R\) gives the same order:

\[
\boxed{
\#\{\text{parallel chord pairs of diameter }O(R)\}
\ll R^4.
}
\tag{4.4}
\]

Hence, subject only to the nondegeneracy/content lemma,

\[
R\le p^{1/2}
\quad\Longrightarrow\quad
\text{local contribution }=O(p^2).
\tag{4.5}
\]

This is a genuine partial result: all configurations whose four endpoints lie in one \(O(\sqrt p)\) window are harmless.

## 4.2 The currently unconditional threshold

Without proving that \(\mathscr P_{h,k,d}\) is nonzero modulo \(p\), the only universal bound for each fixed triple is \(p\) choices of \(x\). Thus

\[
\mathcal N(H,K,D)\ll pHKD.
\tag{4.6}
\]

For \(H,K,D\le R\), this is

\[
pR^3.
\]

Therefore the completely unconditional localization threshold is only

\[
\boxed{
R\le p^{1/3}.
}
\tag{4.7}
\]

A uniform content/nondegeneracy theorem improves \(p^{1/3}\) to \(p^{1/2}\).

## 4.3 Why short \(h,k\) alone are insufficient

If \(h\le H\) and \(k\le K\) but the bridge \(d\) ranges through all of \(\mathbf F_p\), then (4.2) gives schematically

\[
\sum_{h\le H}\sum_{k\le K}\sum_{d<p}
\min\{p,d+h+k\}
\asymp HKp^2.
\tag{4.8}
\]

Even \(H,K\) growing like a small power of \(p\) therefore lose immediately. The long bridge, not the local chord lengths, is the hard variable.

---

# 5. What an optimistic Lang--Weil argument would yield

Suppose, contrary to the actual continuant audit, that after removing forced components the fixed-\((h,k)\) locus were a single absolutely irreducible plane curve of degree

\[
d_{h,k}\ll h+k.
\]

Hasse--Weil/Bombieri would then give

\[
C_{h,k}
=
p+O\bigl((h+k)^2\sqrt p\bigr)
\tag{5.1}
\]

up to lower-order boundary corrections.

The main term \(p\) matches

\[
\frac{M_hM_k}{p+1}=p+O(1+r_h+r_k).
\]

Summing the absolute individual errors over \(h,k\le R\) gives

\[
\sqrt p
\sum_{h,k\le R}(h+k)^2
\asymp
\sqrt p\,R^4.
\tag{5.2}
\]

For this to be \(O(p^2)\) one needs

\[
\boxed{R\le p^{3/8}.}
\tag{5.3}
\]

Thus even the optimistic bounded-degree plane-curve strategy would not reach \(p^{1/2}\) by individual absolute estimates.

More importantly, the premise fails: the bridge \(y-x\) makes the global degree comparable to \(p\). A direct Lang--Weil theorem on the full four-variable incidence variety would generically give a \(p^{5/2}\) error around its \(p^3\) main term, whereas the desired centered error is \(O(p^2)\). One needs an additional half-power of cancellation beyond generic point counting.

This is why the problem is genuinely a dispersion/large-sieve problem rather than merely a curve-counting problem.

---

# 6. Exact Plücker and cocycle identities for long gaps

For any four indices \(r,s,t,u\), the rank-two determinant kernel satisfies

\[
\boxed{
K(r,s)K(t,u)-K(r,t)K(s,u)+K(r,u)K(s,t)=0.
}
\tag{6.1}
\]

## 6.1 Cross-ratio form of the secant certificate

Applying (6.1) to \((x,x+h,y,y+k)\) gives

\[
K(x,x+h)K(y,y+k)
-K(x,y)K(x+h,y+k)
+K(x,y+k)K(x+h,y)=0.
\]

A direct rearrangement yields

\[
\boxed{
\begin{aligned}
K(x,y)\Pi_{h,k}(x,y)
={}&[K(x+h,y)-K(x,y)]\\
&\times[K(x,y+k)-K(x,y)]\\
&+K(x,x+h)K(y,y+k).
\end{aligned}
}
\tag{6.2}
\]

When \(K(x,y)\ne0\), parallelism is equivalent to

\[
\boxed{
\left(
\frac{K(x+h,y)}{K(x,y)}-1
\right)
\left(
\frac{K(x,y+k)}{K(x,y)}-1
\right)
=
-\frac{K(x,x+h)K(y,y+k)}{K(x,y)^2}.
}
\tag{6.3}
\]

This is an exact multiplicative cross-ratio equation. It exhibits the local short kernels on the right, but it still contains the long bridge \(K(x,y)\) and two adjacent long-bridge ratios.

## 6.2 Midpoint composition

For every \(z\) with

\[
\kappa_z:=K(z,z+1)=-\frac6{(z+1)^3}\ne0,
\]

Plücker gives

\[
\boxed{
K(r,s)
=
\frac{
K(r,z+1)K(z,s)-K(r,z)K(z+1,s)
}{\kappa_z}.
}
\tag{6.4}
\]

This is the exact Green-kernel composition law.

Define the two boundary coordinates of a chord by

\[
\mathbf c_z(r,s)
=
\begin{pmatrix}
K(s,z+1)-K(r,z+1)\\
K(z,s)-K(z,r)
\end{pmatrix}.
\tag{6.5}
\]

Since \((Q_z,Q_{z+1})\) is a basis,

\[
Q_s-Q_r
=
\frac{c_{z,1}(r,s)}{\kappa_z}Q_z
+
\frac{c_{z,2}(r,s)}{\kappa_z}Q_{z+1}.
\tag{6.6}
\]

Therefore

\[
\boxed{
\det(Q_s-Q_r,Q_v-Q_u)
=
\frac{
\det(\mathbf c_z(r,s),\mathbf c_z(u,v))
}{\kappa_z}.
}
\tag{6.7}
\]

In particular,

\[
\Pi_{h,k}(x,y)=0
\iff
\mathbf c_z(x,x+h)
\parallel
\mathbf c_z(y,y+k).
\tag{6.8}
\]

If \(z\) is chosen near the midpoint of the union of the four endpoints, every kernel on the right of (6.5) has roughly half the original span. Repeating this construction gives a dyadic recursion of depth \(O(\log p)\) with exactly two boundary channels at every level.

## 6.3 What the recursion accomplishes—and what it does not

The identity proves that long gaps can be assembled from shorter gaps without increasing the state dimension. This is the strongest exact consequence of rank two.

It does **not** reduce algebraic complexity. After recursive splitting, the two coordinates are still deterministic products of the prescribed transfer matrices. Full generation of \(\mathrm{PGL}_2(\mathbf F_p)\) does not imply mixing of this one ordered word, and no cancellation follows from (6.4) alone.

A repair would be a **two-channel flattening theorem**: after one dyadic split, the projective distributions of the boundary-coordinate vectors in (6.5) must have a uniformly bounded second singular value when averaged over the base and gap blocks. Proving precisely that theorem is equivalent in scale to the large-sieve estimate below.

---

# 7. The exact large-sieve formulation

Define the centered direction vector

\[
f_h(\xi)
=P_{h,\xi}-\frac{M_h}{p+1}.
\tag{7.1}
\]

Its Gram matrix is

\[
G_{h,k}
=\langle f_h,f_k\rangle
=C_{h,k}-\frac{M_hM_k}{p+1}.
\tag{7.2}
\]

Then

\[
V_2(p)=\mathbf1^TG\mathbf1.
\tag{7.3}
\]

## 7.1 Robust operator form

A sufficient large-sieve theorem is

\[
\boxed{
\sum_{\xi\in\mathbf P^1(\mathbf F_p)}
\left|
\sum_{h\in\mathcal H}c_hf_h(\xi)
\right|^2
\ll
p\sum_{h\in\mathcal H}|c_h|^2
}
\tag{LS}
\]

for all complex coefficients \(c_h\). Equivalently,

\[
\|G\|_{\mathrm{op}}\ll p.
\]

Taking \(c_h=1\) gives

\[
V_2(p)\ll p|\mathcal H|\ll p^2.
\]

## 7.2 Dyadic operator form

It is enough to prove (LS) separately on every dyadic gap block

\[
\mathcal H_H=\{h:H<h\le2H\}.
\]

Suppose

\[
\left\|
\sum_{h\in\mathcal H_H}c_hf_h
\right\|_2^2
\ll
p\sum_{h\in\mathcal H_H}|c_h|^2.
\tag{7.4}
\]

For \(c_h=1\),

\[
\left\|
\sum_{h\in\mathcal H_H}f_h
\right\|_2
\ll\sqrt{pH}.
\]

The dyadic blocks grow geometrically, so

\[
\sum_H\sqrt H\ll\sqrt p.
\]

By the triangle inequality in \(\ell^2(\mathbf P^1)\),

\[
\left\|\sum_hf_h\right\|_2
\le
\sum_H\left\|\sum_{h\in\mathcal H_H}f_h\right\|_2
\ll p.
\]

Thus the dyadic version also gives \(V_2(p)\ll p^2\) without a logarithmic loss.

## 7.3 Minimal scalar dyadic form

For the actual theorem one does not need all coefficients. A weaker sufficient statement is

\[
\boxed{
\left|
\sum_{h\in\mathcal H_H}
\sum_{k\in\mathcal H_K}
\left(
C_{h,k}-\frac{M_hM_k}{p+1}
\right)
\right|
\ll
p\sqrt{HK}.
}
\tag{DLS}
\]

Indeed,

\[
\sum_{H,K}p\sqrt{HK}
=p\left(\sum_H\sqrt H\right)^2
\ll p^2.
\]

(DLS) is the weakest clean theorem produced by the dyadic program. It is strictly weaker than the operator large sieve and should be treated as the immediate target.

## 7.4 Dual form

The dual of (7.4) is: for every function

\[
g:\mathbf P^1(\mathbf F_p)\to\mathbf C,
\]

\[
\boxed{
\sum_{h\in\mathcal H_H}
\left|
\sum_{x\in\mathcal X_h}g(\Theta_h(x))
-
\frac{M_h}{p+1}\sum_\xi g(\xi)
\right|^2
\ll
p\sum_\xi|g(\xi)|^2.
}
\tag{7.5}
\]

This is the precise quasi-orthogonality statement for the family of maps \(\Theta_h\).

---

# 8. Fourier sums required by the large sieve

For a chord difference \(v\in\mathbf F_p^2\setminus\{0\}\), define

\[
\mu_h(v)
=
\#\{x\in\mathcal X_h:\Delta_h(x)=v\}.
\]

Its Fourier transform is

\[
\widehat\mu_h(\omega)
=
\sum_{x\in\mathcal X_h}
 e_p\bigl(\omega\cdot\Delta_h(x)\bigr).
\tag{8.1}
\]

For a representative vector of \(\xi\), additive orthogonality gives

\[
P_{h,\xi}
=
\frac1p
\sum_{t\in\mathbf F_p}
\widehat\mu_h(t\xi).
\tag{8.2}
\]

Therefore

\[
\boxed{
 f_h(\xi)
 =
 \frac1p\sum_{t\ne0}\widehat\mu_h(t\xi)
 +\frac{M_h}{p(p+1)}.
}
\tag{8.3}
\]

Thus (LS) is a **radial Fourier large sieve**: it asks for cancellation after summing the orbit-increment Fourier coefficients over every nonzero radial line

\[
\{t\xi:t\in\mathbf F_p^\times\}.
\]

## 8.1 The explicit orbit sums

For a solution direction \(\xi=[c:d]\), put

\[
u_n^{\xi}=ca_n+db_n.
\]

The basic sums are

\[
\boxed{
S_h(t;\xi)
=
\sum_{x\in\mathcal X_h}
 e_p\left(t\bigl(u_{x+h}^{\xi}-u_x^{\xi}\bigr)\right).
}
\tag{8.4}
\]

By (2.2),

\[
\begin{aligned}
u_{x+h}^{\xi}-u_x^{\xi}
={}&
\frac{N_h(x)}{Q_h(x)}u_{x+1}^{\xi}\\
&+
\left(
-\frac{(x+1)^3N_{h-1}(x+1)}{Q_h(x)}-1
\right)u_x^{\xi}.
\end{aligned}
\tag{8.5}
\]

The coefficients in (8.5) have degree \(O(h)\), but the state

\[
x\longmapsto(u_x^{\xi},u_{x+1}^{\xi})
\]

is the distinguished nonautonomous Apéry orbit. It is not a bounded-degree polynomial map and is not known to be a bounded-conductor trace function in \(x\).

This is exactly where standard Weil and Deligne estimates stop.

## 8.2 Why ordinary Parseval is one factor too weak

Parseval on \(\mathbf F_p^2\) gives

\[
\sum_{\omega\in\mathbf F_p^2}
|\widehat\mu_h(\omega)|^2
=
p^2\sum_v\mu_h(v)^2.
\tag{8.6}
\]

Even if the difference map is nearly injective,

\[
\sum_v\mu_h(v)^2\asymp p,
\]

so the right side is \(\asymp p^3\).

Applying Cauchy--Schwarz to the radial sum in (8.3) loses another factor \(p\). It yields a large-sieve constant of order \(p^2\), whereas (LS) needs order \(p\).

Therefore global Fourier energy or fixed-frequency square-root cancellation is not enough. One needs cancellation **inside the radial sums and across the gap family simultaneously**.

## 8.3 The continuant loop

If one expands the left side of (LS) and sums over directions, additive orthogonality enforces

\[
\det(\Delta_h(x),\Delta_k(y))=0,
\]

which is precisely

\[
\Pi_{h,k}(x,y)=0.
\]

Thus using continuants to bound the Fourier sums returns exactly to the parallel-secant certificate. The large sieve is not a repackaging that removes the hard term; it is the correct statement of the cancellation that the certificate must supply.

---

# 9. Minimal new lemmas

The program isolates the following hierarchy.

## Lemma U — universal-pair budget

\[
\boxed{
U_p=\sum_{h\in\mathcal H}r_h\ll p.
}
\tag{U}
\]

The stronger expected statement is

\[
U_p=\frac{p-1}{2}.
\]

This is independent of the pair-variance estimate and is needed because universal pairs contribute to every direction.

A possible algebraic formulation uses the two coefficient equations in

\[
u_{x+h}-u_x
=
\frac{N_h(x)}{Q_h(x)}u_{x+1}
+
\left(
-\frac{(x+1)^3N_{h-1}(x+1)}{Q_h(x)}-1
\right)u_x.
\]

A universal return requires both coefficients to vanish. Proving that their common roots consist only of the forced reflection point, or have bounded average over \(h\), would prove (U).

## Lemma C — content/nondegeneracy for local bridges

Outside the diagonal and palindromic forced configurations, the cleared polynomial

\[
\mathscr P_{h,k,d}(x)
\]

must not vanish identically modulo \(p\).

A sufficient uniform form is

\[
\boxed{
\mathscr P_{h,k,d}\not\equiv0\pmod p
}
\tag{C}
\]

for every admissible nonforced triple with total span \(<p\).

Together with the degree calculation, (C) proves the \(O(R^4)\) local-diameter theorem up to \(R=p^{1/2}\).

This lemma is concrete and likely attackable by leading coefficients, contents, resultants, and the reflection involution. It is useful, but it does not treat long bridges.

## Lemma D — dyadic scalar dispersion

\[
\boxed{
\left|
\sum_{h\sim H}\sum_{k\sim K}
\left(
C_{h,k}-\frac{M_hM_k}{p+1}
\right)
\right|
\ll p\sqrt{HK}.
}
\tag{D}
\]

This, together with (U), is the minimal theorem that closes the pair-variance route.

## Lemma LS — projective operator large sieve

The stronger and more stable form is (LS):

\[
\left\|\sum_hc_hf_h\right\|_2^2
\ll p\sum_h|c_h|^2.
\]

This would control arbitrary weighted gap ranges and would likely be the form naturally produced by an automorphic, sheaf-theoretic, or expander argument.

## Lemma F — two-channel flattening for segment products

A concrete route to (D) or (LS) would be a theorem that the two boundary-coordinate channels

\[
\mathbf c_z(r,s)
\]

from (6.5), after one dyadic split, have projective second singular value of the random scale uniformly over the left/right segment blocks.

This is a deterministic mixing theorem for consecutive Apéry transfer products. Existing random-walk expansion results do not apply because the increments are neither random nor selected from a fixed distribution.

## What is *not* the missing lemma

The estimate

\[
\#\{x:N_h(x)=0\}\le3(h-1)
\]

is immediate from the degree and is not close to the core difficulty. It controls one prime/gap polynomial. The missing statement controls the centered correlation of two **different bases and gaps** after averaging over the full bridge variable.

---

# 10. Final assessment of the five proposed steps

## Step 1 — exact variance expansion

**Completed.** Equations (1.7), (1.9), and (1.11) give the exact main term, state-return correction, and forced palindromic contribution.

A separate \(U_p=O(p)\) lemma is required.

## Step 2 — short blocks by degree or Lang--Weil

**Partially successful.**

- Trivially, endpoint diameter \(R\le p^{1/3}\) contributes \(O(p^2)\).
- With the nondegeneracy lemma (C), endpoint diameter \(R\le p^{1/2}\) contributes \(O(p^2)\).
- Short chord gaps without short bridge do not have bounded degree.
- Even the optimistic false degree-\(O(h+k)\) plane-curve model reaches only \(p^{3/8}\) by individual Hasse--Weil errors.

Thus degree theory handles a genuine local portion but not the long-bridge mass.

## Step 3 — long gaps via Plücker

**Algebraically completed, analytically open.** Equations (6.4)--(6.8) give an exact rank-two dyadic recursion. The recursion preserves two channels and halves spans, but it supplies no cancellation for the deterministic segment products.

The repair is Lemma F, a two-channel flattening theorem.

## Step 4 — large sieve for \(\Theta_h\)

**Precisely formulated.** The minimal scalar form is (D); the robust operator form is (LS); the dual form is (7.5); and the required exponential sums are (8.4).

Current continuant identities do not bound those sums because their phases contain the full orbit state.

## Step 5 — minimal new inputs

The exact list is:

1. \(U_p\ll p\);
2. local content/nondegeneracy (C);
3. dyadic scalar dispersion (D), or preferably the operator large sieve (LS);
4. a two-channel segment-product flattening theorem as a proposed mechanism for (D).

Only items 1 and 3 are theorem-closing. Item 2 proves the maximal degree-theoretic local range. Item 4 is the most faithful structural route to item 3.

---

# 11. Recommended endgame

The best next sequence of attacks is:

1. **Prove or isolate the universal-return gcd.** Compute
   \[
   \gcd\left(
   N_h(x),
   (x+1)^3N_{h-1}(x+1)+Q_h(x)
   \right)
   \]
   symbolically and conjecture its exact forced factor. This could remove the separate \(U_p\) gap.

2. **Prove the local content lemma.** For each order chamber, derive formulas such as (3.2), compute their leading coefficient and content, and classify all identically zero cases. This turns the experimentally observed local randomness into a rigorous \(R\le\sqrt p\) theorem.

3. **Measure the dyadic Gram matrix.** For
   \[
   G_{h,k}=C_{h,k}-\frac{M_hM_k}{p+1},
   \]
   compute operator norms of dyadic submatrices, not only the all-ones quadratic form. Test whether
   \[
   \|G_{H,K}\|_{\mathrm{op}}/p
   \]
   remains bounded and whether off-diagonal dyadic blocks decay with scale separation.

4. **Test the Plücker split numerically.** At a midpoint \(z\), record the projective boundary-coordinate vectors \([\mathbf c_z(r,s)]\). Determine whether one dyadic split reduces their block discrepancy and whether the two channels behave like an expander step.

5. **Aim first for the scalar theorem (D).** It is strictly weaker than a full large sieve and is exactly sufficient. A proof may exploit cancellation between dyadic \((h,k)\) blocks that an individual-curve argument destroys.

The program has therefore not collapsed. It has reached a clean endgame:

\[
\boxed{
\text{local continuant geometry is controlled;}\quad
\text{long bridges require a two-channel dyadic dispersion theorem.}
\]

---

# References and project state

- [Current project Proposition A and pair-variance criterion](https://github.com/xiangyazi24/zinan-memory/commit/83f35eedceafae65f6f4a113a483f8b4bc2e7b65)
- [Green-function rank-two endpoint formula](https://github.com/xiangyazi24/zinan-memory/commit/21e64e816909c11745ffb3cb76b6c5f41066c409)
- E. Bombieri, *On exponential sums in finite fields*, Amer. J. Math. 88 (1966), 71--105.
- E. Kowalski, [*The large sieve, monodromy and zeta functions of curves*](https://arxiv.org/abs/math/0503714).
- M. Rudnev, [*On the number of incidences between points and planes in three dimensions*](https://arxiv.org/abs/1407.0426).

The large-sieve-for-Frobenius framework requires a fixed bounded-complexity algebraic family. The present maps \(\Theta_h\) have complexity carried by the deterministic Apéry prefix products, so the existing theorem is a model for the desired mechanism rather than a black-box solution.