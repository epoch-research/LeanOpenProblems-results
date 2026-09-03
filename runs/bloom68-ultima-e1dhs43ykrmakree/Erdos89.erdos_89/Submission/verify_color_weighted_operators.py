#!/usr/bin/env python3
"""Exact checks for color_weighted_operator_analysis.md.

No numerical clustering of distances is used: coordinates and squared distances
are integers or Fractions. Floating-point norm computations are only sanity
checks of explicit factorization or Hadamard/Rayleigh bounds. The five-point
parameter identity is also checked by exact symbolic rational arithmetic.
"""
from collections import Counter
from fractions import Fraction as F
from math import isqrt
import numpy as np


def d2(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def palette(points):
    c = Counter()
    for i, p in enumerate(points):
        for q in points[i + 1:]:
            s = d2(p, q)
            assert s > 0
            c[s] += 1
    return c  # UNORDERED counts. Ordered r_s = 2*c[s].


def hadamard(m):
    assert m > 0 and m & (m - 1) == 0
    h = np.array([[(-1) ** ((i & j).bit_count()) for j in range(m)]
                  for i in range(m)], dtype=np.int64)
    assert np.array_equal(h @ h.T, m * np.eye(m, dtype=np.int64))
    assert int(h.sum()) == m
    return h


def core(m):
    # Dividing all coordinates by B places A near 0 and B near 1.
    # All positive core distances are distinct, by binary expansion/valuation.
    B = 2 ** (4 * m)
    p = [(-2 ** i, 0) for i in range(m)]
    p += [(B + 2 ** (m + j), 0) for j in range(m)]
    assert len(palette(p)) == len(p) * (len(p) - 1) // 2
    return p, B


def multiplicity_padding(m):
    p, B = core(m)
    h = hadamard(m)
    counts = palette(p)
    bad = [(i, j) for i in range(m) for j in range(m) if h[i, j] == -1]
    candidate = 0
    for i, j in bad:
        ell = p[m + j][0] - p[i][0]
        target = ell * ell
        assert counts[target] == 1
        while True:
            candidate += 1
            t = candidate
            u, v = (2 * B + t, t * t), (2 * B + t, t * t + ell)
            new = [d2(u, x) for x in p] + [d2(v, x) for x in p]
            if (min(new) > 0 and len(set(new)) == len(new)
                    and not set(new).intersection(counts)):
                break
        p.extend([u, v])
        counts.update(new)
        counts[target] += 1
    assert candidate * candidate <= B  # Our examples also have bounded diameter/B.
    assert counts == palette(p)
    q, n = len(bad), len(p)
    assert q == m * (m - 1) // 2
    assert n == m * m + m
    assert set(counts.values()).issubset({1, 2})
    assert sum(v == 2 for v in counts.values()) == q
    for i in range(m):
        for j in range(m):
            r = 2 * counts[d2(p[i], p[m + j])]
            assert F(1, r) == F(3, 8) + F(int(h[i, j]), 8)
    Q = n * (n - 1) // 2
    D = len(counts)
    E = sum((2 * v) ** 2 for v in counts.values())
    M = n * (n - 1)
    assert D == Q - q
    assert E == 4 * Q + 8 * q
    assert F(E * D, M * M) == 1 + F(q * (Q - 2 * q), Q * Q)
    # Exact Rayleigh quotient of (W_AB o H) on the all-ones vector.
    rayleigh = F(m + 3, 8)
    test = 3 * h.astype(float) / 8 + np.ones((m, m)) / 8
    norm_ratio = np.linalg.norm(test, 2) / np.sqrt(m)
    assert norm_ratio + 1e-12 >= float(rayleigh) / np.sqrt(m)
    print(f"Hadamard padding m={m}: n={n}, D={D}, E={E}, "
          f"ED/M^2={float(F(E*D, M*M)):.8f}; "
          f"Schur test={norm_ratio:.8f}, certified >= {(m+3)/(8*np.sqrt(m)):.8f}; "
          f"last translation parameter={candidate}")
    return p, counts


def degree_padding(m):
    p, B = core(m)
    h = hadamard(m)
    counts = palette(p)
    bad = [(i, j) for i in range(m) for j in range(m) if h[i, j] == -1]
    parameter = 0
    for i, j in bad:
        ell = p[m + j][0] - p[i][0]
        target = ell * ell
        assert counts[target] == 1
        for anchor in (i, m + j):
            while True:
                parameter += 1
                t = parameter
                ux, uy = F(1 - t*t, 1 + t*t), F(2*t, 1 + t*t)
                a = p[anchor]
                u = (a[0] + ell*ux, a[1] + ell*uy)
                ds = [d2(u, x) for x in p]
                assert ds[anchor] == target
                other = ds[:anchor] + ds[anchor + 1:]
                if (min(ds) > 0 and len(set(other)) == len(other)
                        and not set(other).intersection(counts)):
                    break
            p.append(u)
            counts.update(ds)
        assert counts[target] == 3
    assert counts == palette(p)
    n, q = len(p), len(bad)
    assert n == m*m + m
    assert set(counts.values()).issubset({1, 3})
    for i in range(m):
        for j in range(m):
            s = d2(p[i], p[m+j])
            ki = sum(d2(p[i], x) == s for x in p)
            kj = sum(d2(p[m+j], x) == s for x in p)
            expected = 1 if h[i, j] == 1 else 2
            assert ki == kj == expected
            # Both row normalization and symmetric degree normalization.
            assert F(1, ki) == F(3, 4) + F(int(h[i, j]), 4)
            assert ki * kj == expected * expected
    Q = n*(n-1)//2
    D = len(counts)
    E = sum((2*v)**2 for v in counts.values())
    assert D == Q - 2*q and E == 4*Q + 24*q
    print(f"Inverse-degree padding m={m}: n={n}, D={D}, E={E}; "
          "all repeated colors have ordered multiplicity 6, "
          "and the exact core weights are 1 or 1/2.")


def radial_projection(points, X):
    n = len(points)
    counts = palette(points)
    coefficients = {s: F(0) for s in counts}
    for i in range(n):
        for j in range(n):
            if i != j:
                coefficients[d2(points[i], points[j])] += X[i][j]
    for s in counts:
        coefficients[s] /= 2*counts[s]
    diag = sum(X[i][i] for i in range(n)) / n
    return [[diag if i == j else coefficients[d2(points[i], points[j])]
             for j in range(n)] for i in range(n)]


def projection_checks():
    p = [(i, j) for i in range(3) for j in range(3)]
    n = len(p)
    X = [[F((3*i + 5*j) % 11 - 5) for j in range(n)] for i in range(n)]
    Y = radial_projection(p, X)
    assert radial_projection(p, Y) == Y
    assert sum(Y[i][i] for i in range(n)) == sum(X[i][i] for i in range(n))
    I = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    J = [[F(1) for j in range(n)] for i in range(n)]
    assert radial_projection(p, I) == I
    assert radial_projection(p, J) == J
    # Rank-one PSD input, opposite-corner edge of longest color r_s=4.
    v = [F(0)]*n
    v[0], v[-1] = F(1), F(-1)
    X = [[v[i]*v[j] for j in range(n)] for i in range(n)]
    Y = radial_projection(p, X)
    witness = Y[0][0] + Y[-1][-1] + Y[0][-1] + Y[-1][0]
    assert witness == F(4, n) - 1 == F(-5, 9)
    print("Color projection: exact idempotence, trace preservation, Pi(I)=I, Pi(J)=J.")
    print(f"3x3 grid PSD counterexample: (e_0+e_8)^T Pi(vv^T)(e_0+e_8)={witness}.")
    p20 = [(i, j) for i in range(20) for j in range(20)]
    c20 = palette(p20)
    assert 2*c20[2*19*19] == 4
    print(f"20x20 grid: n=400, D={len(c20)} < (n-1)/2, longest color has r=4.")


def grid_schur_checks():
    for L in (3, 8, 20):
        p = [(i, j) for i in range(L) for j in range(L)]
        c = palette(p)
        # Exact multiplicity lower bound used in the uniform row factorization.
        for a in range(-(L-1), L):
            for b in range(-(L-1), L):
                if a or b:
                    assert 2*c[a*a+b*b] >= 2*(L-abs(a))*(L-abs(b))
        maxrow = 0.0
        for i, x in enumerate(p):
            row2 = sum(1.0/(2*c[d2(x,y)])**2 for j,y in enumerate(p) if i != j)
            maxrow = max(maxrow, row2)
        assert np.sqrt(maxrow) <= np.pi**2/6
        print(f"Grid L={L}: exact displacement multiplicity inequalities checked; "
              f"maximum row-l2 norm of W = {np.sqrt(maxrow):.10f}; "
              "uniform Schur bound <= pi^2/6, lower bound >= 1/4.")


def weighted_cauchy_checks():
    p = [(0, 0), (1, 0), (3, 0), (0, 100), (3, 100)]
    counts = palette(p)
    n = len(p)
    re = [[F(0) for _ in p] for _ in p]
    im = [[F(0) for _ in p] for _ in p]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            dx, dy = p[i][0]-p[j][0], p[i][1]-p[j][1]
            s, r = d2(p[i], p[j]), 2*counts[d2(p[i], p[j])]
            re[i][j], im[i][j] = F(dx, s*r), F(-dy, s*r)
            # [Z,C]_ij = 1/r, exactly, including its imaginary part.
            assert dx*re[i][j] - dy*im[i][j] == F(1, r)
            assert dx*im[i][j] + dy*re[i][j] == 0
            # Color inverse identity C_s=[Z*,A_s]/s.
            assert dx*dx + dy*dy == s
    frob = sum(re[i][j]**2 + im[i][j]**2 for i in range(n) for j in range(n))
    assert frob == sum(F(1, 2*v*s) for s, v in counts.items())
    rows = sum(sum(re[i])**2 + sum(im[i])**2 for i in range(n))
    assert rows < frob
    assert rows <= F(n, 2)*frob
    real_moment = sum(p[i][0]*sum(re[i]) - p[i][1]*sum(im[i]) for i in range(n))
    imag_moment = sum(p[i][0]*sum(im[i]) + p[i][1]*sum(re[i]) for i in range(n))
    assert real_moment == F(len(counts), 2) and imag_moment == 0
    mx, my = F(sum(x for x,y in p), n), F(sum(y for x,y in p), n)
    variance = sum((x-mx)**2+(y-my)**2 for x,y in p)
    sum_sr = sum(2*v*s for s,v in counts.items())
    assert sum_sr == 2*n*variance
    assert len(counts)**2 <= sum_sr*frob
    t = 100
    deficit_formula = F(-t**6+15*t**4+146*t*t+158,
                        8*(t*t+1)*(t*t+4)*(t*t+9))
    assert rows-frob == deficit_formula
    # Exact contribution of the collinear triangle (0,1,3).
    gamma = F(1, 12) - F(1, 4) + F(1, 24)
    assert gamma == F(-1, 8)
    assert 2*counts[1] == 2 and 2*counts[4] == 2 and 2*counts[9] == 4
    print("Weighted commutator and Frobenius identities checked exactly on a full-planar example.")
    print(f"Triangle contribution={gamma}; global row/Frobenius squared ratio={float(rows/frob):.10f} < 1.")
    print(f"Exact global row-energy minus Frobenius-energy: {rows-frob}")


def path_internal(m, T):
    r = {1: 2*(m-1)}
    r.update({k: 2*(m-k+T) for k in range(2, m)})
    frob = sum(F(1, k*k*r[k]) for k in range(1, m))
    rows = F(0)
    for i in range(m):
        h = sum(F(1, (i-j)*r[abs(i-j)]) for j in range(m) if i != j)
        rows += h*h
    rows += sum(2*T*F(1, k*r[k])**2 for k in range(2, m))
    return frob, rows


def suppression_checks():
    print("Exact block computations and rigorous cross-block error certificates:")
    for m in (8, 32, 128):
        T = m**4
        n = m + 2*T*(m-2)
        R = n*n*m*m
        frob, rows = path_internal(m, T)
        # Gadget centers at j*(R+2*m)*i give every inter-block distance >= R.
        # ||K 1||^2 <= n^3/(4R^2); ||h_internal+K1||^2 <= 2||h_internal||^2+2||K1||^2.
        certificate = (2*rows + F(n**3, 2*R**2))/frob
        assert certificate < F(3, m-1)
        print(f"  m={m}, T=m^4, n={n}: internal ratio={float(rows/frob):.10f}; "
              f"actual full-plane ratio <= {float(certificate):.10f}; "
              f"limit as T,R -> infinity = 1/(m-1)={1/(m-1):.10f}.")


def symbolic_five_point_deficit():
    import sympy as sp
    t = sp.symbols('t', positive=True)
    z = [sp.Integer(0), sp.Integer(1), sp.Integer(3), sp.I*t, 3+sp.I*t]
    rs = {(0,1):2, (0,2):4, (0,3):4, (0,4):4, (1,2):2,
          (1,3):2, (1,4):2, (2,3):4, (2,4):4, (3,4):4}
    C = sp.zeros(5)
    for (i,j), r in rs.items():
        C[i,j] = sp.Integer(1)/(r*(z[i]-z[j]))
        C[j,i] = -C[i,j]
    h = C*sp.ones(5,1)
    deficit = (h.conjugate().T*h)[0] - sp.trace(C.conjugate().T*C)
    expected = (-t**6+15*t**4+146*t**2+158)/(8*(t**2+1)*(t**2+4)*(t**2+9))
    assert sp.cancel(sp.expand(deficit-expected)) == 0
    print("Symbolic five-point deficit for all t>3 verified exactly as a rational function.")


def main():
    projection_checks()
    grid_schur_checks()
    weighted_cauchy_checks()
    symbolic_five_point_deficit()
    for m in (4, 8, 16):
        multiplicity_padding(m)
    # Large exact Hadamard certificate, without constructing thousands of gadgets.
    h = hadamard(256)
    assert int(h.sum()) == 256
    print("Hadamard m=256 analytic certificate: n=65792, ||M_W|| >= 259/128 = 2.0234375; "
          "||Pi|| >= 259/64 = 4.046875.")
    degree_padding(4)
    suppression_checks()
    print("ALL CHECKS PASSED. Computations verify examples/identities, not the unsolved amplification.")


if __name__ == '__main__':
    main()
