#!/usr/bin/env python3
"""Weakly nonlinear and finite-difference continuation probe.

The steady flux equation is integrated once using the Neumann boundary
conditions.  Thus every positive steady state satisfies

    H_m(u) - chi * log(1 + v) = C,
    H_m'(u) = u**(-m).

The finite-difference solve below enforces this relation at every node,
the elliptic equation with reflected ghost points (Neumann BC), the
trapezoidal mass constraint, and a prescribed first cosine coefficient.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import numpy as np
from scipy.optimize import root, brentq
from scipy.sparse import coo_matrix


PI = np.pi


def weak_coefficients(m: float, ustar: float, discrete_n: int | None = None):
    """Return (chi_lin, a2, S, chi2), where chi2=chi_lin*S.

    With u-U = eps*cos(pi*x) + eps**2*a2*cos(2*pi*x) + ...,
    chi = chi_lin + eps**2*chi2 + ... .  If discrete_n is supplied,
    use the eigenvalues of the second-order Neumann finite difference
    operator on discrete_n subintervals.
    """
    if discrete_n is None:
        lam1 = PI**2
        lam2 = (2 * PI) ** 2
    else:
        h = 1.0 / discrete_n
        lam1 = 4.0 / h**2 * np.sin(PI / (2 * discrete_n)) ** 2
        lam2 = 4.0 / h**2 * np.sin(PI / discrete_n) ** 2
    r1 = 1.0 / (1.0 + lam1)
    r2 = 1.0 / (1.0 + lam2)
    b = 1.0 + ustar
    chi_lin = b / (r1 * ustar**m)
    a2 = (m / ustar - r1 / b) / (4.0 * (1.0 - r2 / r1))
    s = (
        0.5 * a2 * (r2 / b - m / ustar)
        + m * (m + 1.0) / (8.0 * ustar**2)
        - r1**2 / (4.0 * b**2)
    )
    return chi_lin, a2, s, chi_lin * s


def critical_m(ustar: float) -> float:
    def f(m):
        return weak_coefficients(m, ustar)[2]

    return brentq(f, 1.0, 8.0)


def hfun(u: np.ndarray, m: float) -> np.ndarray:
    if abs(m - 1.0) < 1e-14:
        return np.log(u)
    return u ** (1.0 - m) / (1.0 - m)


@dataclass
class FDSolution:
    amplitude: float
    chi: float
    residual_inf: float
    nfev: int
    u: np.ndarray
    v: np.ndarray
    c: float


class FDSystem:
    def __init__(self, m: float, ustar: float, n_intervals: int):
        self.m = m
        self.ustar = ustar
        self.N = n_intervals
        self.n = n_intervals + 1
        self.h = 1.0 / n_intervals
        self.x = np.linspace(0.0, 1.0, self.n)
        self.c1 = np.cos(PI * self.x)
        self.c2 = np.cos(2.0 * PI * self.x)
        self.weights = np.ones(self.n)
        self.weights[[0, -1]] = 0.5

    def unpack(self, y):
        n = self.n
        return y[:n], y[n : 2 * n], y[-2], y[-1]

    def residual(self, y, amplitude):
        u, v, c, chi = self.unpack(y)
        n, h = self.n, self.h
        out = np.empty(2 * n + 2)
        out[:n] = hfun(u, self.m) - chi * np.log1p(v) - c

        # -v_xx + v - u = 0; reflected ghost points impose v_x=0.
        ell = out[n : 2 * n]
        ell[0] = -2.0 * (v[1] - v[0]) / h**2 + v[0] - u[0]
        ell[-1] = -2.0 * (v[-2] - v[-1]) / h**2 + v[-1] - u[-1]
        ell[1:-1] = (
            -(v[:-2] - 2.0 * v[1:-1] + v[2:]) / h**2
            + v[1:-1]
            - u[1:-1]
        )
        out[-2] = h * np.dot(self.weights, u) - self.ustar
        out[-1] = (
            2.0 * h * np.dot(self.weights * self.c1, u - self.ustar)
            - amplitude
        )
        return out

    def jacobian(self, y, amplitude):
        del amplitude
        u, v, c, chi = self.unpack(y)
        n, h = self.n, self.h
        rows: list[int] = []
        cols: list[int] = []
        data: list[float] = []

        # Integrated flux relation.
        for i in range(n):
            rows.extend((i, i, i, i))
            cols.extend((i, n + i, 2 * n, 2 * n + 1))
            data.extend((u[i] ** (-self.m), -chi / (1.0 + v[i]), -1.0, -np.log1p(v[i])))

        # Elliptic finite difference equations.
        for i in range(n):
            row = n + i
            rows.append(row)
            cols.append(i)
            data.append(-1.0)
            rows.append(row)
            cols.append(n + i)
            data.append(1.0 + (2.0 / h**2))
            if i == 0:
                rows.append(row)
                cols.append(n + 1)
                data.append(-2.0 / h**2)
            elif i == n - 1:
                rows.append(row)
                cols.append(n + n - 2)
                data.append(-2.0 / h**2)
            else:
                rows.extend((row, row))
                cols.extend((n + i - 1, n + i + 1))
                data.extend((-1.0 / h**2, -1.0 / h**2))

        for i in range(n):
            rows.extend((2 * n, 2 * n + 1))
            cols.extend((i, i))
            data.extend((h * self.weights[i], 2.0 * h * self.weights[i] * self.c1[i]))
        return coo_matrix((data, (rows, cols)), shape=(2 * n + 2, 2 * n + 2)).tocsr()

    def initial_guess(self, amplitude):
        chi0, a2, _, chi2 = weak_coefficients(self.m, self.ustar, self.N)
        u = self.ustar + amplitude * self.c1 + amplitude**2 * a2 * self.c2
        # Calculate the discrete elliptic response directly from eigenvalues.
        h = self.h
        lam1 = 4.0 / h**2 * np.sin(PI / (2 * self.N)) ** 2
        lam2 = 4.0 / h**2 * np.sin(PI / self.N) ** 2
        r1 = 1.0 / (1.0 + lam1)
        r2 = 1.0 / (1.0 + lam2)
        v = self.ustar + amplitude * r1 * self.c1 + amplitude**2 * a2 * r2 * self.c2
        chi = chi0 + amplitude**2 * chi2
        c = self.h * np.dot(self.weights, hfun(u, self.m) - chi * np.log1p(v))
        return np.r_[u, v, c, chi]

    def solve(self, amplitude, y0=None):
        if y0 is None:
            y0 = self.initial_guess(amplitude)
        ans = root(
            lambda y: self.residual(y, amplitude),
            y0,
            jac=lambda y: self.jacobian(y, amplitude).toarray(),
            method="hybr",
            options={"xtol": 1e-10, "maxfev": 1000},
        )
        residual_inf = np.linalg.norm(self.residual(ans.x, amplitude), ord=np.inf)
        if not ans.success and residual_inf > 1e-8:
            raise RuntimeError(ans.message)
        if np.min(ans.x[: self.n]) <= 0 or np.min(ans.x[self.n : 2 * self.n]) <= -1 or ans.x[-1] <= 0:
            raise RuntimeError("Newton solve left the positive physical branch")
        u, v, c, chi = self.unpack(ans.x)
        return ans.x, FDSolution(
            amplitude=amplitude,
            chi=chi,
            residual_inf=residual_inf,
            nfev=ans.nfev,
            u=u,
            v=v,
            c=c,
        )


def continuation(m, ustar, n_intervals, relative_amplitudes):
    system = FDSystem(m, ustar, n_intervals)
    solutions = []
    y = None
    for relamp in relative_amplitudes:
        amp = relamp * ustar
        # The asymptotic guess is more accurate than recycling a solution at a
        # different amplitude when the requested amplitudes are very small.
        y, sol = system.solve(amp, None)
        solutions.append(sol)
    return solutions


def first_mode_amplitude(system: FDSystem, y: np.ndarray) -> float:
    u = y[: system.n]
    return 2.0 * system.h * np.dot(
        system.weights * system.c1, u - system.ustar
    )


def pseudo_arclength(m, ustar, n_intervals, relamp0=0.005, relamp1=0.0075, steps=6):
    """Continue the nonconstant branch with secant-predictor arclength steps."""
    system = FDSystem(m, ustar, n_intervals)
    y0, _ = system.solve(relamp0 * ustar)
    y1, _ = system.solve(relamp1 * ustar)
    points = [y0, y1]
    for _ in range(steps):
        tangent = y1 - y0
        ds = np.linalg.norm(tangent)
        tangent /= ds
        predicted = y1 + ds * tangent

        def augmented_residual(y):
            physical = system.residual(y, 0.0)[:-1]
            return np.r_[physical, np.dot(y - predicted, tangent)]

        def augmented_jacobian(y):
            physical = system.jacobian(y, 0.0).toarray()[:-1, :]
            return np.vstack((physical, tangent))

        ans = root(
            augmented_residual,
            predicted,
            jac=augmented_jacobian,
            method="hybr",
            options={"xtol": 1e-10, "maxfev": 1000},
        )
        residual_inf = np.linalg.norm(augmented_residual(ans.x), ord=np.inf)
        if not ans.success and residual_inf > 1e-8:
            raise RuntimeError(ans.message)
        y0, y1 = y1, ans.x
        points.append(y1)
    return system, points


def print_weak_table():
    ms = (1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 6.0)
    us = (0.5, 1.0, 2.0)
    print("WEAKLY NONLINEAR COEFFICIENTS")
    print("U       m         chi_lin              chi2  direction")
    for ustar in us:
        for m in ms:
            chi0, _, _, chi2 = weak_coefficients(m, ustar)
            direction = "super" if chi2 > 0 else "sub"
            print(f"{ustar:3.1f}  {m:6.2f}  {chi0:14.8f}  {chi2:16.9g}  {direction}")
        print(f"critical m at U={ustar:g}: {critical_m(ustar):.12f}")


def print_continuation(m, ustar, n_intervals, relamps):
    sols = continuation(m, ustar, n_intervals, relamps)
    chi0h, _, _, chi2h = weak_coefficients(m, ustar, n_intervals)
    x = np.array([s.amplitude**2 for s in sols])
    y = np.array([s.chi for s in sols])
    # Fit chi-chi0h = c2*A^2 + c4*A^4 + c6*A^6.
    design = np.column_stack((x, x**2, x**3))
    coeff, *_ = np.linalg.lstsq(design, y - chi0h, rcond=None)
    print(f"FD CONTINUATION m={m:g}, U={ustar:g}, N={n_intervals}")
    print(f"chi_lin,h={chi0h:.12g}, analytic chi2,h={chi2h:.12g}, fitted chi2={coeff[0]:.12g}")
    print("A/U            chi          chi-chi_lin,h       residual_inf")
    for s in sols:
        print(f"{s.amplitude/ustar:7.4f}  {s.chi:14.10g}  {s.chi-chi0h:17.9g}  {s.residual_inf:.3e}")


def print_arclength(m, ustar, n_intervals):
    system, points = pseudo_arclength(m, ustar, n_intervals)
    chi0h = weak_coefficients(m, ustar, n_intervals)[0]
    print(f"PSEUDO-ARCLENGTH m={m:g}, U={ustar:g}, N={n_intervals}")
    print("step       A/U              chi        chi-chi_lin,h")
    for i, y in enumerate(points):
        amp = first_mode_amplitude(system, y)
        print(f"{i:4d}  {amp/ustar:9.6f}  {y[-1]:14.10g}  {y[-1]-chi0h:17.9g}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--table", action="store_true")
    parser.add_argument("--m", type=float)
    parser.add_argument("--u", type=float)
    parser.add_argument("--N", type=int, default=160)
    parser.add_argument("--arclength", action="store_true")
    parser.add_argument(
        "--relamps",
        type=float,
        nargs="*",
        default=(0.005, 0.0075, 0.01, 0.0125, 0.015, 0.02),
    )
    args = parser.parse_args()
    if args.table or args.m is None or args.u is None:
        print_weak_table()
    if args.m is not None and args.u is not None:
        if args.arclength:
            print_arclength(args.m, args.u, args.N)
        else:
            print_continuation(args.m, args.u, args.N, args.relamps)


if __name__ == "__main__":
    main()
