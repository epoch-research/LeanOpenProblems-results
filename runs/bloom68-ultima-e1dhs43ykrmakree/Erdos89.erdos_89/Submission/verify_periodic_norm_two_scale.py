#!/usr/bin/env python3
"""Exact finite checks for periodic_norm_two_scale.md. No Lean changes.
The analytic asymptotics are proved in the note, not inferred from these tests.
Only the displayed K ratios and limiting constants use floating point.
"""
from array import array
from collections import deque
from math import gcd, isqrt, log, pi


def sieve_spf(N):
    spf = array('I', [0]) * (N + 1)
    for p in range(2, isqrt(N) + 1):
        if spf[p] == 0:
            for n in range(p * p, N + 1, p):
                if spf[n] == 0:
                    spf[n] = p
    return spf


def factor(n, spf):
    ans = []
    while n > 1:
        p = spf[n] or n
        k = 0
        while n % p == 0:
            n //= p
            k += 1
        ans.append((p, k))
    return ans


class OrbitMonoid:
    def __init__(self, M):
        self.M = M

        def canonical(a, b):
            return min((a % M, b % M), (-b % M, a % M),
                       (-a % M, -b % M), (b % M, -a % M))

        self.reps = sorted({canonical(a, b) for a in range(M) for b in range(M)})
        index = {c: j for j, c in enumerate(self.reps)}
        self.ids = [[index[canonical(a, b)] for b in range(M)] for a in range(M)]
        self.one = self.cls(1, 0)
        self.mul = [[self.cls(a*c-b*d, a*d+b*c) for c, d in self.reps]
                    for a, b in self.reps]
        self.conj = [self.cls(a, -b) for a, b in self.reps]
        self.units = [j for j, (a, b) in enumerate(self.reps)
                      if gcd(a*a+b*b, M) == 1]

    def cls(self, a, b):
        return self.ids[a % self.M][b % self.M]

    def prod(self, A, B):
        return frozenset(self.mul[a][b] for a in A for b in B)

    def power(self, a, k):
        r = self.one
        for _ in range(k):
            r = self.mul[r][a]
        return r


def direct_states(M, N):
    mon = OrbitMonoid(M)
    W = [set() for _ in range(N + 1)]
    first = {}
    for a in range(isqrt(N) + 1):
        for b in range(isqrt(N - a*a) + 1):
            n = a*a+b*b
            if n:
                W[n].add(mon.cls(a, b))
                first.setdefault(n, (a, b))
    return mon, list(map(frozenset, W)), first


def check_exact_states():
    N = 2000
    spf = sieve_spf(N)
    total = 0
    for M in [1, 2, 3, 4, 5, 8, 13, 15, 20]:
        mon, W, first = direct_states(M, N)
        local = {}
        for p in range(2, N + 1):
            if spf[p]:
                continue
            pk, k = p, 1
            while pk <= N:
                if p == 2:
                    T = frozenset([mon.power(mon.cls(1, 1), k)])
                elif p % 4 == 3:
                    T = (frozenset() if k % 2 else
                         frozenset([mon.power(mon.cls(p, 0), k // 2)]))
                else:
                    a, b = first[p]
                    c, d = mon.cls(a, b), mon.cls(a, -b)
                    T = frozenset(mon.mul[mon.power(c, j)][mon.power(d, k-j)]
                                  for j in range(k + 1))
                assert T == W[pk], (M, p, k)
                local[p, k] = T
                pk *= p
                k += 1
        for n in range(1, N + 1):
            T = frozenset([mon.one])
            for p, k in factor(n, spf):
                T = mon.prod(T, local[p, k])
            assert T == W[n], (M, n)
            total += 1
        pairs = 0
        for a in range(1, N + 1):
            for b in range(1, N // a + 1):
                if gcd(a, b) == 1:
                    assert mon.prod(W[a], W[b]) == W[a*b]
                    pairs += 1
        print(f"M={M:2d}: {len(mon.reps):3d} residue/unit orbits; "
              f"all {N} Euler states and {pairs} coprime products checked")
    print(f"Exact prime-power/Euler reconstruction: {total} integers checked.")


def matmul(A, B):
    n = len(A)
    C = [[0] * n for _ in range(n)]
    for i, row in enumerate(A):
        for k, a in enumerate(row):
            if a:
                for j, b in enumerate(B[k]):
                    C[i][j] += a * b
    return C


def minus_scalar(A, t):
    B = [row[:] for row in A]
    for j in range(len(B)):
        B[j][j] -= t
    return B


def check_mod13_group_and_nilpotence():
    mon = OrbitMonoid(13)
    G = mon.units
    H = [c for c in G if sum(t*t for t in mon.reps[c]) % 13 == 1]
    K = [c for c in G if mon.conj[c] == c]
    assert (len(G), len(H), len(K)) == (36, 3, 12)
    assert set(H) & set(K) == {mon.one}
    assert {sum(t*t for t in mon.reps[c]) % 13 for c in K} == set(range(1, 13))
    assert mon.cls(2, 6) in H and mon.cls(2, 6) != mon.one
    generators = [frozenset([c, mon.conj[c]]) for c in G]
    states = [frozenset([mon.one])]
    index = {states[0]: 0}
    queue = deque(states)
    while queue:
        S = queue.popleft()
        for T in generators:
            U = mon.prod(S, T)
            if U not in index:
                index[U] = len(states)
                states.append(U)
                queue.append(U)
    assert len(states) == 36
    # W=72V, not V: rational split primes have total density 1/2.
    W = [[0] * len(states) for _ in states]
    for j, S in enumerate(states):
        for T in generators:
            W[index[mon.prod(S, T)]][j] += 1
    assert all(sum(row[j] for row in W) == 36 for j in range(len(W)))
    squarefree = matmul(matmul(W, minus_scalar(W, 36)), minus_scalar(W, 12))
    annihilator = matmul(squarefree, minus_scalar(W, 12))
    assert not any(any(row) for row in annihilator)
    assert any(any(row) for row in squarefree)
    print("Mod 13: |G|=36, |ker N|=3, |Fix(conjugation)|=12; "
          "N maps Fix(conjugation) bijectively onto F_13^*.")
    print("36-state unit submonoid: 2V is column stochastic; "
          "V(V-1/2)(V-1/6)^2=0 but V(V-1/2)(V-1/6)!=0.")
    print("Thus lower-spectrum nilpotence is real, not safely discardable.")


def norm_support(M, B, radius):
    out = set()
    for a, b in B:
        x0 = a + M * ((-radius - a + M - 1) // M)
        for x in range(x0, radius + 1, M):
            ybound = isqrt(radius*radius-x*x)
            y0 = b + M * ((-ybound - b + M - 1) // M)
            for y in range(y0, ybound + 1, M):
                n = x*x+y*y
                if n:
                    out.add(n)
    return out


def check_missing_mod13(N=1_000_000):
    spf = sieve_spf(N)
    norms = bytearray(N + 1)
    active = bytearray(N + 1)
    for a in range(isqrt(N) + 1):
        aa = a*a
        for b in range(isqrt(N - aa) + 1):
            n = aa + b*b
            if not n:
                continue
            norms[n] = 1
            if n > 2 and not spf[n] and n % 4 == 1 and n != 13:
                is_active = a*b*(a-b)*(a+b) % 13 != 0
                if is_active:
                    active[n] = 1
    actual = bytearray(N + 1)
    for n in norm_support(13, {(0, 0), (2, 6), (11, 7)}, isqrt(N)):
        actual[n] = 1
    # N is a square, so norm_support uses exactly the intended height.
    assert isqrt(N)**2 == N
    avoid = bytearray(N + 1)
    avoid[1] = 1
    for n in range(2, N + 1):
        p = spf[n] or n
        avoid[n] = avoid[n // p] and not active[p]
    totals = [0, 0, 0, 0]
    rows = []
    for n in range(1, N + 1):
        local = bool(norms[n] and (n % 13 == 1 or n % 169 == 0))
        missing = local and not actual[n]
        predicted = bool(norms[n] and n % 13 == 1 and avoid[n])
        assert missing == predicted, n
        assert not actual[n] or local, n
        for j, a in enumerate((norms[n], local, actual[n], missing)):
            totals[j] += a
        if n in [1, 40, 1000, 10000, 100000, N]:
            rows.append((n, *totals))
    print("Mod-13 exact missing-set characterization checked at every n<=1,000,000:")
    print("  missing iff n is a norm, n=1 mod 13, and no active split prime divides n.")
    print("          X       S(X)       C_B(X)       F_B(X)       missing")
    for row in rows:
        print("  " + " ".join(f"{v:11d}" for v in row))


def points(M, A, radius):
    P = []
    for x in range(-radius, radius + 1):
        bnd = isqrt(radius*radius-x*x)
        for y in range(-bnd, bnd + 1):
            if (x % M, y % M) in A:
                P.append((x, y))
    return P


def distances(P):
    D = set()
    for j, (a, b) in enumerate(P):
        for c, d in P[:j]:
            D.add((a-c)**2+(b-d)**2)
    return D


def check_actual_endpoints():
    kappa = 0.7642236535892207  # display only
    gamma = (pi/(4*kappa))**2
    print(f"Display constants: gamma={gamma:.12f}, "
          f"gamma*log(4)={gamma*log(4):.12f}, "
          f"gamma*log(2)={gamma*log(2):.12f}")
    print("Actual endpoints at BOTH scales (finite values are not asymptotic evidence):")
    print(" M    R     n_R   D_R  n_(R/2) D_(R/2) K_R^2-K_(R/2)^2  half-size radius,n")
    for M, A, radii in [(1, {(0, 0)}, [8, 16, 24]),
                         (5, {(0, 0)}, [20, 40, 80]),
                         (13, {(0, 0), (2, 6)}, [52, 104, 208])]:
        B = {((a-c) % M, (b-d) % M) for a, b in A for c, d in A}
        for R in radii:
            P, Q = points(M, A, R), points(M, A, R // 2)
            DP, DQ = distances(P), distances(Q)
            FF = norm_support(M, B, 2*R)
            assert DP <= FF
            inner = {m for m in FF if (t := 4*R*R+2*M*M-m) >= 0
                     and t*t >= 32*R*R*M*M}
            assert inner <= DP
            err = len(FF)-len(DP)
            assert err <= 1 or (err-1)**2 <= 32*M*M*R*R
            assert 2 <= len(Q) <= len(P)//2
            r = (isqrt(2*(R-M)**2)-M)//2
            Qh = points(M, A, r)
            assert 2 <= len(Qh) <= len(P)//2
            defect = (len(P)/len(DP))**2-(len(Q)/len(DQ))**2
            print(f"{M:2d} {R:5d} {len(P):7d} {len(DP):5d} {len(Q):7d} "
                  f"{len(DQ):5d} {defect:17.9f}   {r:4d},{len(Qh)}")
    print("Every endpoint sandwich, O(MR) boundary count, and half-size test passed.")
    print(f"Mod-13 predicted limiting centered-half defect: {gamma*log(4)/49:.12f}")


def check_annulus_encoding():
    print("Varying-modulus annuli: exact centered child has n=2,D=1.")
    print(" R     M      n      actual D    actual centered defect")
    for R in [8, 16, 32]:
        P = [(x, y) for x in range(-R, R+1)
             for y in range(-isqrt(R*R-x*x), isqrt(R*R-x*x)+1)
             if 4*(x*x+y*y) > R*R]
        P += [(0, 0), (1, 0)]
        M = 5*R
        A = {(x % M, y % M) for x, y in P}
        assert set(points(M, A, R)) == set(P)
        Q = points(M, A, R // 2)
        assert set(Q) == {(0, 0), (1, 0)}
        DD = distances(P)
        assert distances(Q) == {1}
        B = {((a-c) % M, (b-d) % M) for a, b in P for c, d in P}
        assert norm_support(M, B, 2*R) == DD
        print(f"{R:3d} {M:5d} {len(P):7d} {len(DD):11d} "
              f"{(len(P)/len(DD))**2-4:24.9f}")
    print("Unboundedness for this sequence is proved analytically in the note;")
    print("it refutes only a modulus-uniform CENTERED selector, not arbitrary selection.")


def main():
    check_exact_states()
    check_mod13_group_and_nilpotence()
    check_missing_mod13()
    check_actual_endpoints()
    check_annulus_encoding()
    print("ALL EXACT FINITE CHECKS PASSED. No numerical claim of proving a limit.")


if __name__ == '__main__':
    main()
