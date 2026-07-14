ANSWER Q4825 9bccef0c

# Problem 3.1: the \(7_2(-1)\) Seifert endpoint, its Godbillon–Vey value, and the endpoint-shape certificate

## Executive answer

With the standard meridian–longitude surgery convention and the standard orientation of the Brieskorn link, the \(-1\) filling of the five-twist knot is

\[
\boxed{S^3_{-1}(7_2)\cong \Sigma(2,3,17).}
\]

A normalized set of oriented Seifert invariants is

\[
\boxed{
M_\beta
=M\bigl(0;-2;(2,1),(3,2),(17,14)\bigr).
}
\tag{0.1}
\]

The opposite orientation is equivalently

\[
-M_\beta
=M\bigl(0;-1;(2,1),(3,1),(17,3)\bigr).
\tag{0.2}
\]

For (0.1),

\[
e(M_\beta)
=-2+\frac12+\frac23+\frac{14}{17}
=-\frac1{102},
\tag{0.3}
\]

and the orbifold Euler characteristic is

\[
\chi_{\rm orb}
=2-3+\frac12+\frac13+\frac1{17}
=-\frac{11}{102}.
\tag{0.4}
\]

Consequently the Brooks–Goldman Seifert volume is

\[
\boxed{
\{M_\beta\}
=\frac{4\pi^2\chi_{\rm orb}^2}{|e(M_\beta)|}
=\frac{242\pi^2}{51}.
}
\tag{0.5}
\]

For the maximal, orbifold-uniformizing \({\rm PSL}_2(\mathbb R)\) representation, in the oriented convention in which the signed Brooks–Goldman invariant is

\[
GV(\rho)=\frac{4\pi^2\chi_{\rm orb}^2}{e(M)},
\]

one obtains

\[
\boxed{
GV(\rho_{\rm Fuch})=-\frac{242\pi^2}{51}.
}
\tag{0.6}
\]

Thus the natural exact answer for the beta character is

\[
\boxed{
GV(\rho_\beta)=-\frac{242\pi^2}{51},
}
\tag{0.7}
\]

**provided one verifies that the beta intersection character is the maximal Fuchsian character with the indicated lift.** The topology of the filled manifold determines the absolute maximum (0.5), but it does not, by itself, prove that an arbitrarily selected representation realizes that maximum or fix its sign. The missing representation-level check is finite: compute the three elliptic rotation numbers of the filled character and its central lift, or prove uniqueness of the purely hyperbolic intersection on the chosen lifted component. This is exactly what Khoi did for the analogous \(5_2(1)=\Sigma(2,3,11)\) endpoint.

There is also a normalization correction to the proposed target identity. In Khoi's convention, if

\[
a=\log M,\qquad b=\log L,
\]

then

\[
GV(\rho_\beta)-GV(\rho_\alpha)
=4\int(\dot a b-a\dot b)\,dt
=-4\int\bigl(a\,db-b\,da\bigr).
\tag{0.8}
\]

Therefore the challenge integral

\[
\int_\alpha^\beta
\left(\log M\,\frac{dL}{L}
      -\log L\,\frac{dM}{M}\right)
=\frac{4\pi^2}{85}
\]

corresponds to

\[
\boxed{
GV(\rho_\beta)-GV(\rho_\alpha)
=-\frac{16\pi^2}{85},
}
\tag{0.9}
\]

not \(+4\pi^2/85\). If one instead defines the renormalized invariant

\[
\mathcal G(\rho):=-\frac14GV(\rho),
\]

then \(\mathcal G(\rho_\beta)-\mathcal G(\rho_\alpha)=4\pi^2/85\).

Combining (0.7) and (0.9) gives the conditional exact alpha value

\[
\boxed{
GV(\rho_\alpha)
=-\frac{1162\pi^2}{255}.
}
\tag{0.10}
\]

The tetrahedral part requires a second correction. The polynomial

\[
3w^5-10w^4+13w^3-10w^2+4w-1
\]

and the four formulas quoted in the question describe the **complete-cusp** solution (up to shape permutations and \(z,z',z''\) changes). They are not the beta filling shapes. At beta one must solve the incomplete gluing equations together with \(M=L\). An exact algebraic system for doing so is given in Section 4.

Finally, the ordinary principal-branch Rogers sum is not a topological invariant at a real endpoint. The relevant object is an **extended Rogers dilogarithm with integral flattenings**. There is no reason for the unflattened sum to be an integer multiple of \(\pi^2/6\); in fact, the signed GV value itself satisfies

\[
\frac{-242\pi^2/51}{\pi^2/6}
=-\frac{484}{17},
\]

which is not an integer.

---

# 1. Identification of the \(-1\) filling

The knot \(7_2\) is the five-twist knot. In the standard twist-knot surgery family, the homology-sphere Seifert filling is

\[
S^3_{-1}(7_2)\cong\Sigma(2,3,17),
\]

up to simultaneous reversal of the knot/surgery orientation convention. This is the next member of the same family in which Khoi records

\[
S^3_{+1}(5_2)\cong\Sigma(2,3,11).
\]

The third multiplicity is \(6m-1\): for the three-twist knot it is \(11\), and for the five-twist knot it is \(17\).

A useful orientation audit comes from the Casson surgery formula. The normalized Alexander polynomial of \(7_2\) is

\[
\Delta_{7_2}(t)=3t-5+3t^{-1},
\]

so

\[
\Delta_{7_2}''(1)=6.
\]

Hence, with the usual Casson normalization,

\[
\lambda\bigl(S^3_{-1}(7_2)\bigr)=-3.
\]

This agrees with the standard link orientation of \(\Sigma(2,3,17)\); orientation reversal changes the sign.

The small-Seifert nature of the slopes on twist knots is covered by Brittenham–Wu's classification of exceptional surgeries on two-bridge knots. Their classification establishes that the relevant integral slopes are the small-Seifert slopes; the Brieskorn identification is obtained by the standard Kirby-calculus description of the twist-knot surgery family.

---

# 2. Seifert invariants and the Brooks–Goldman calculation

Use the convention

\[
M=M\bigl(g;b;(\alpha_1,\beta_1),\ldots,(\alpha_r,\beta_r)\bigr),
\]

with rational Euler number

\[
e(M)=b+\sum_{j=1}^r\frac{\beta_j}{\alpha_j}.
\]

For

\[
M_\beta=M\bigl(0;-2;(2,1),(3,2),(17,14)\bigr),
\]

one finds

\[
\begin{aligned}
e(M_\beta)
&=-2+\frac12+\frac23+\frac{14}{17}\\
&=\frac{-204+51+68+84}{102}\\
&=-\frac1{102}.
\end{aligned}
\tag{2.1}
\]

The first-homology order is

\[
|H_1(M_\beta;\mathbb Z)|
=\left|2\cdot3\cdot17\,e(M_\beta)\right|
=1,
\]

as required for a Brieskorn homology sphere.

The base orbifold is \(S^2(2,3,17)\), so

\[
\begin{aligned}
\chi_{\rm orb}
&=2-3+\frac12+\frac13+\frac1{17}\\
&=-1+\frac{51+34+6}{102}\\
&=-\frac{11}{102}.
\end{aligned}
\tag{2.2}
\]

Since \(\chi_{\rm orb}<0\) and \(e\ne0\), this is a \(\widetilde{{\rm SL}}_2(\mathbb R)\)-manifold. Brooks and Goldman give

\[
\{M\}=\frac{4\pi^2\chi_{\rm orb}^2}{|e(M)|}.
\]

Substitution yields

\[
\begin{aligned}
\{M_\beta\}
&=4\pi^2
  \frac{121}{102^2}\,102\\
&=\frac{484\pi^2}{102}\\
&=\boxed{\frac{242\pi^2}{51}}.
\end{aligned}
\tag{2.3}
\]

For the uniformizing representation, the signed value is obtained by retaining the sign of \(e\):

\[
GV(\rho_{\rm Fuch})
=\frac{4\pi^2\chi_{\rm orb}^2}{e(M_\beta)}
=-\frac{242\pi^2}{51}.
\tag{2.4}
\]

This is precisely analogous to Khoi's calculation for

\[
5_2(1)=\Sigma(2,3,11),
\]

where

\[
\chi_{\rm orb}=-\frac5{66},\qquad
 e=-\frac1{66},
\]

and therefore

\[
GV=-\frac{50\pi^2}{33},
\]

the value printed in Khoi's paper.

## 2.1 What must be checked for \(\rho_\beta\)

Brooks–Goldman computes the maximum and the uniformizing value. To identify the A-polynomial endpoint representation with that value, one should supply one of the following equivalent certificates.

1. **Rotation-number certificate.** In the Seifert presentation, show that the projective images of the three exceptional-fiber generators have orders \(2,3,17\), with the lift giving orbifold Euler class \(-11/102\).
2. **Uniqueness certificate.** Show that the equation \(M=L\) has exactly one irreducible purely hyperbolic character on the lifted real component followed from the knot complement, and that its filled image is non-elementary.
3. **Triangle-group certificate.** Conjugate the filled representation explicitly to the uniformizing representation of \(\Delta(2,3,17)\), with the central fiber lift agreeing with (0.1).

Without one of these, topology proves only

\[
|GV(\rho_\beta)|\le \frac{242\pi^2}{51},
\]

with equality for the maximal representation.

---

# 3. The factor-of-four normalization in Problem 3.1

Khoi's Schläfli formula uses

\[
GV(\rho_1)-GV(\rho_0)
=4\int(\dot a b-a\dot b)\,dt.
\]

The challenge form is

\[
\omega=a\,db-b\,da
=(a\dot b-b\dot a)\,dt.
\]

Hence

\[
\boxed{dGV=-4\omega.}
\tag{3.1}
\]

If

\[
I_{\alpha\beta}=\int_\alpha^\beta\omega
=\frac{4\pi^2}{85},
\]

then

\[
GV_\beta-GV_\alpha=-4I_{\alpha\beta}
=-\frac{16\pi^2}{85}.
\tag{3.2}
\]

Assuming (0.7),

\[
\begin{aligned}
GV_\alpha
&=GV_\beta+\frac{16\pi^2}{85}\\
&=-\frac{242\pi^2}{51}+\frac{16\pi^2}{85}\\
&=\frac{-1210+48}{255}\pi^2\\
&=\boxed{-\frac{1162\pi^2}{255}}.
\end{aligned}
\tag{3.3}
\]

If the symbol called \(GV\) in a separate note has already been renormalized by \(-1/4\), then the user's \(+4\pi^2/85\) difference is consistent. The normalization must be stated explicitly before comparing endpoint values.

---

# 4. Exact algebraic description of the beta shapes

## 4.1 The complete shape polynomial is not the beta polynomial

The polynomial

\[
3w^5-10w^4+13w^3-10w^2+4w-1=0
\tag{4.1}
\]

is reciprocal to

\[
u^5-4u^4+10u^3-13u^2+10u-3=0
\]

under \(w=1/u\). It describes the complete-cusp algebraic point. The associated formulas

\[
z_0=\frac1{1-w},\qquad
z_1=w,\qquad
z_2=1-\frac1w,\qquad
z_3=-\frac{(1-w)^3}{w}
\]

are therefore complete-structure formulas. They do not remain valid with the same fixed polynomial after imposing the beta filling.

## 4.2 Exact polynomial for the peripheral beta eigenvalue

Let \(s=s_\beta\) be the positive root near \(0.4068\) of

\[
A_{7_2}(s,s)=0.
\]

After removing the nonzero monomial factor \(s^3\), the exact reciprocal polynomial is

\[
\boxed{
\begin{aligned}
f_\beta(s)={}&s^{21}-2s^{20}-3s^{19}+2s^{18}+2s^{17}
 +8s^{16}+6s^{15}+s^{14}\\
&+5s^{13}-4s^{12}
 -4s^9+5s^8+s^7+6s^6+8s^5\\
&+2s^4+2s^3-3s^2-2s+1.
\end{aligned}}
\tag{4.2}
\]

The coefficients of \(s^{11}\) and \(s^{10}\) are zero. The required root is selected by

\[
0<s_\beta<1
\]

and by continuation along the specified positive real A-polynomial branch.

## 4.3 A finite exact gluing chart

A convenient four-tetrahedron deformation chart uses variables \(r\) and

\[
X=M^2.
\]

Put

\[
A_r=X(1-r^2)-r,
\qquad
B_r=1-r^2-rX,
\qquad
C_r=1-r-r^2.
\tag{4.3}
\]

The internal gluing equation is

\[
\boxed{
Xr^4(1-r^2)=A_rB_rC_r.
}
\tag{4.4}
\]

At the beta endpoint \(M=L=s_\beta\), hence \(X=s_\beta^2\). In this chart the squared peripheral equation is

\[
\boxed{
B_r^2=X^3A_r^2.
}
\tag{4.5}
\]

The sign in \(B_r=\pm X^{3/2}A_r\) is fixed by continuous logarithm branches and by the precise preferred-longitude convention. The four ordered shapes are

\[
\boxed{
\begin{aligned}
z_T&=1-r^2,\\
z_U&=\frac{r}{1-r^2},\\
z_V&=\frac{r}{X(1-r^2)},\\
z_W&=\frac1{1-\dfrac{rX}{1-r^2}}.
\end{aligned}}
\tag{4.6}
\]

Thus the beta shapes are exact real algebraic numbers defined by the zero-dimensional ideal

\[
\boxed{
\begin{aligned}
\mathcal I_\beta=\langle{}
&f_\beta(s),\ X-s^2,\\
&Xr^4(1-r^2)-A_rB_rC_r,\\
&B_r^2-X^3A_r^2
\rangle.
\end{aligned}}
\tag{4.7}
\]

Together with the real-component and sign conditions, (4.6)–(4.7) are an exact algebraic specification of all four deformed shapes. Expanded minimal polynomials can be obtained by resultants from (4.7).

There is one essential audit before treating (4.6) as the final peripheral certificate: verify the monomial map from this triangulation's meridian and longitude to the degree-22 A-polynomial convention. Squaring the meridian changes the regulator form by a factor of two, and inverting the preferred longitude reverses its sign. This is the same convention issue that affects (0.8).

---

# 5. Why the ordinary Rogers sum is not the endpoint invariant

For \(0<z<1\), one may write

\[
R(z)=\operatorname{Li}_2(z)
+\frac12\log z\log(1-z)-\frac{\pi^2}{6}.
\]

At a real Seifert endpoint, however, some tetrahedral shapes typically lie in

\[
(-\infty,0)\cup(1,\infty).
\]

Then principal logarithms are not compatible with the lifted gluing equations. Changing a logarithm branch changes the Rogers value by terms involving \(\pi i\log z\) and \(\pi^2\). Consequently

\[
\sum_j R(z_j)
\]

with principal branches is not invariant under:

- changing tetrahedral shape representatives \(z\leftrightarrow z'\leftrightarrow z''\);
- applying a five-term move;
- changing logarithm lifts;
- changing the peripheral lift in \(\widetilde{{\rm SL}}_2(\mathbb R)\).

The correct expression is the extended Rogers regulator

\[
\widehat R(z;p,q)
=\operatorname{Li}_2(z)
+\frac12(\Log z+p\pi i)
          (\Log(1-z)+q\pi i)
-\frac{\pi^2}{6},
\tag{5.1}
\]

with integer flattenings \(p,q\). For orientation signs \(\epsilon_j\), define

\[
\widehat{\mathcal R}_\beta
=\sum_{j=1}^4\epsilon_j
  \widehat R(z_j;p_j,q_j).
\tag{5.2}
\]

The flattening integers must solve the internal edge equations and the chosen peripheral lift. Only (5.2), modulo the appropriate period lattice, is related to the Chern–Simons/Godbillon–Vey invariant.

Therefore the requested comparison with an **integer** multiple of \(\pi^2/6\) is not the right test. In the normalization where the extended regulator is identified with the signed GV value,

\[
\frac{GV(\rho_\beta)}{\pi^2/6}
=-\frac{484}{17},
\tag{5.3}
\]

which has denominator \(17\). Other common regulator normalizations introduce factors of \(2\) or \(4\), but they do not turn the unflattened principal sum into a canonical integer.

## 5.1 Finite certificate for the beta Rogers value

A machine-checkable endpoint computation consists of the following exact data.

1. Isolate the intended real solution of (4.7).
2. Record the four oriented shapes (4.6).
3. Continue logarithms from the complete component to determine \((p_j,q_j)\).
4. Verify every internal edge flattening equation exactly.
5. Verify the primitive meridian–longitude exponent vectors.
6. Evaluate (5.2), reducing by extended five-term relations.
7. Check that the result agrees, in the chosen normalization and period lattice, with
   \[
   -\frac{242\pi^2}{51}.
   \]

This is the required Rogers-dilogarithm certificate. Evaluating four ordinary principal-branch dilogarithms is not a substitute for Steps 3–6.

---

# 6. What is proved, and what remains conditional

The following statements are exact:

\[
S^3_{-1}(7_2)\cong\Sigma(2,3,17)
\]

up to the explicitly stated orientation convention;

\[
M_\beta=M(0;-2;(2,1),(3,2),(17,14));
\]

\[
e=-\frac1{102},\qquad
\chi_{\rm orb}=-\frac{11}{102};
\]

and

\[
\{M_\beta\}=\frac{242\pi^2}{51}.
\]

The signed formula

\[
GV(\rho_\beta)=-\frac{242\pi^2}{51}
\]

is exact for the maximal Fuchsian representation and is the intended beta value if the endpoint character is certified to be that representation with the indicated lift.

The remaining nontrivial endpoint work is not the Brooks–Goldman arithmetic. It is:

- identifying the beta A-polynomial character with the maximal triangle-group character;
- fixing the meridian/longitude and orientation conventions;
- solving the deformed shape ideal on the correct real branch;
- and computing an integral flattening for the extended Rogers sum.

---

# References

1. Mark Brittenham and Ying-Qing Wu, *The classification of exceptional Dehn surgeries on 2-bridge knots*, Communications in Analysis and Geometry 9 (2001), 97–113; arXiv:math/0011005.
2. Vu The Khoi, *On the integral of \(\log x\,dy/y-\log y\,dx/x\) over the A-polynomial curves*, Acta Math. Vietnam. 33 (2008), 519–528; arXiv:0811.2725.
3. R. Brooks and W. Goldman, *Volumes in Seifert space*, Duke Math. J. 51 (1984), 529–545.
4. R. Brooks and W. Goldman, *The Godbillon–Vey invariant of a transversely homogeneous foliation*, Trans. Amer. Math. Soc. 286 (1984), 651–664.
5. Walter D. Neumann, *Extended Bloch group and the Cheeger–Chern–Simons class*, Geom. Topol. 8 (2004), 413–474.
6. Christian K. Zickert, *The volume and Chern–Simons invariant of a representation*, Duke Math. J. 150 (2009), 489–532; arXiv:0710.2049.
