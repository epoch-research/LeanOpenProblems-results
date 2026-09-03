#!/usr/bin/env python3
"""Finite checks for UnsignedFeedbackResearch.md; not asymptotic proofs.

Uses actual prime divisors of positive integers. No Lean files are read.
"""
from collections import defaultdict
from fractions import Fraction
from math import log


def sieve(limit):
    lpf = [1] * (limit + 1)
    rad = [1] * (limit + 1)
    primes = []
    for p in range(2, limit + 1):
        if lpf[p] == 1:
            primes.append(p)
            for n in range(p, limit + 1, p):
                lpf[n] = p
                rad[n] *= p
    return primes, lpf, rad


def sgn(x):
    return (x > 0) - (x < 0)


def exact_identities(X):
    primes, lpf, _ = sieve(X + 1)
    trunc = [1] * (X + 2)
    a = [0] * X
    S = 0
    records = []
    cofactor_checks = 0
    for p in primes:
        assert a == [sgn(trunc[n + 1] - trunc[n]) for n in range(1, X + 1)]
        H = [int(n % p == 0 or (n + 1) % p == 0) for n in range(1, X + 1)]
        T = sum(v * h for v, h in zip(a, H))
        R = Fraction(T) - Fraction(2 * S, p)
        u = p * R / X
        if p > 2:
            assert all(v in (-1, 1) for v in a)
            assert abs(u) <= 5
        records.append((p, u, S, T))
        if p > 2 and p * p > X + 1:
            paired = 0
            for k in range(2, X // p + 1):
                Pk = lpf[k]
                minus = int(trunc[k * p - 1] < Pk)
                plus = int(trunc[k * p + 1] < Pk)
                paired += 2 * (minus - plus)
                for m, F in ((k * p - 1, minus), (k * p + 1, plus)):
                    expanded = int(lpf[m] < Pk)
                    for r in range(1, k):
                        if m % r == 0 and lpf[r] < Pk:
                            q = m // r
                            expanded += int(q > p and lpf[q] == q)
                    assert F == expanded
                    cofactor_checks += 1
            if (X + 1) % p == 0:
                paired += a[-1]
            assert paired == T
        oldS = S
        for m in range(p, X + 2, p):
            trunc[m] = p
        a = [sgn(trunc[n + 1] - trunc[n]) for n in range(1, X + 1)]
        S = sum(a)
        assert S == oldS - T + int((X + 1) % p == 0)
        assert S == (1 - Fraction(2, p)) * oldS - R + int((X + 1) % p == 0)
    assert S == sum(sgn(lpf[n + 1] - lpf[n]) for n in range(1, X + 1))
    w = Fraction(1)
    boundary = feedback = mass_all = mass_odd = J = Fraction(0)
    w2 = None
    for p, u, _, _ in reversed(records):
        mass_all += 2 * w / p
        if (X + 1) % p == 0:
            boundary += w
        if p > 2:
            mass_odd += 2 * w / p
            feedback += w * u / p
            J += w * u * u / p
        else:
            w2 = w
        w *= 1 - Fraction(2, p)
    assert mass_all == 1
    assert mass_odd == 1 - w2
    assert S == boundary - X * feedback
    # Cauchy--Schwarz in a rational form.
    assert feedback * feedback <= J * mass_odd / 2
    return cofactor_checks


def refine(ids, values):
    lookup = {}
    ans = []
    for g, v in zip(ids, values):
        key = (g, v)
        if key not in lookup:
            lookup[key] = len(lookup)
        ans.append(lookup[key])
    return ans


def groups(ids):
    out = defaultdict(list)
    for i, g in enumerate(ids):
        out[g].append(i)
    return list(out.values())


def kl_bernoulli(v, q):
    z = 0.0
    if v:
        z += v * log(v / q)
    if v < 1:
        z += (1 - v) * log((1 - v) / (1 - q))
    return z


def divisor_moment_test(limit=5000):
    from math import comb
    _, lpf, _ = sieve(limit + 1)
    omega = [0] * (limit + 2)
    tau4 = [1] * (limit + 2)
    for n in range(2, limit + 2):
        p, m, e = lpf[n], n, 0
        while m % p == 0:
            m //= p
            e += 1
        omega[n] = omega[m] + 1
        tau4[n] = tau4[m] * comb(e + 3, 3)
        assert 4 ** omega[n] <= tau4[n]
    H = Fraction(0)
    total_tau = 0
    for Y in range(1, limit + 1):
        H += Fraction(1, Y)
        total_tau += tau4[Y]
        if Y in (50, 200, 1000, limit):
            assert total_tau <= Y * H ** 3
            s = sum(2 ** (omega[n] + omega[n + 1]) for n in range(1, Y + 1))
            s0 = sum(4 ** omega[n] for n in range(1, Y + 1))
            s1 = sum(4 ** omega[n + 1] for n in range(1, Y + 1))
            assert s * s <= s0 * s1
    print(f'PASS exact divisor/Cauchy moment inequalities through {limit}')



def filtration_test(X):
    primes, lpf, rad = sieve(X + 1)
    a = [0] * X
    U = [0] * X
    F = [0] * X
    D = [1] * X
    d0, d1 = [1] * X, [1] * X
    omega = [0] * X
    E = VU = VF = KG = infoU = info_lower = vf_lower = vu_lower = 0.0
    tvF = tv_lower = 0.0
    good_count = atom_checks = quotient_checks = 0
    min_p = X + 1
    for p in primes:
        if p ** 10 > X ** 9:
            break
        L = [int((n + 1) % p == 0) - int(n % p == 0) for n in range(1, X + 1)]
        H = [abs(v) for v in L]
        if p ** 4 > X ** 3 and p > 2:
            min_p = min(min_p, p)
            q = sum(H) / X
            assert 0 < q < 1
            u = (p * sum(ai * h for ai, h in zip(a, H)) - 2 * sum(a)) / X
            E += u * u / p
            good = [i for i in range(X)
                    if max(lpf[i + 1], lpf[i + 2]) == p
                    and rad[i + 1] * rad[i + 2] // p > 2 * X + 1]
            good_count += len(good)
            vf_lower += p * len(good) / X * (1 - 2 / p) ** 2
            tv_lower += len(good) / X * (1 - 2 / p)
            split_groups = defaultdict(list)
            for i in range(X):
                assert d0[i] * d1[i] == D[i]
                split_groups[tuple(sorted((d0[i], d1[i])))].append(i)
            for g in split_groups.values():
                z = sum(a[i] * (H[i] - 2 / p) for i in g) / len(g)
                KG += p * len(g) / X * z * z
                if D[g[0]] > 2 * X + 1:
                    assert len(g) == 1
                    quotient_checks += 1
            for ids, mode in ((U, 'U'), (F, 'F')):
                local_var = local_info = 0.0
                K = 1
                blocked_hits = 0
                for g in groups(ids):
                    h = sum(H[i] for i in g)
                    v = h / len(g)
                    local_var += p * len(g) / X * (v - 2 / p) ** 2
                    local_info += len(g) / X * kl_bernoulli(v, q)
                    if mode == 'F':
                        tvF += len(g) / X * abs(v - 2 / p)
                    if D[g[0]] > X:
                        assert all(D[i] == D[g[0]] for i in g)
                        assert len(g) <= 2 ** omega[g[0]]
                        if mode == 'F':
                            assert len(g) == 1
                        else:
                            K = max(K, len(g))
                            blocked_hits += h
                        atom_checks += 1
                if mode == 'U':
                    VU += local_var
                    infoU += local_info
                    lower = max(0, log(1 / q) - log(K) - 1) * blocked_hits / X
                    assert local_info + 1e-12 >= lower
                    info_lower += lower
                    lower_var = ((p / K) * (1 - 2 * K / p) ** 2 * blocked_hits / X
                                 if p > 2 * K else 0.0)
                    assert local_var + 1e-10 >= lower_var
                    vu_lower += lower_var
                else:
                    VF += local_var
                    index_sizes = {i: len(g) for g in groups(ids) for i in g}
                    assert all(index_sizes[i] == 1 and H[i] == 1 for i in good)
                    assert all(a[i] in (-1, 1) for i in good)
        U = refine(U, H)
        F = refine(F, L)
        for i in range(X):
            if H[i]:
                D[i] *= p
                if L[i] == -1:
                    d0[i] *= p
                else:
                    d1[i] *= p
                omega[i] += 1
                a[i] = L[i]
        # The nested winner and hit history recover the labelled ternary history.
        assert all(L[i] == H[i] * a[i] for i in range(X))
    assert VF + 1e-9 >= vf_lower
    assert KG + 1e-9 >= vf_lower
    assert VU + 1e-9 >= vu_lower
    assert tvF + 1e-9 >= tv_lower
    print(f"filtration X={X}: band=(X^.75,X^.9], good-largest-hit mass={good_count/X:.8f}")
    print(f"  feedback energy={E:.10f}, predictable V_U={VU:.8f}, V_F={VF:.8f}, K_G={KG:.8f}")
    print(f"  I(H_p;unlabelled past) sum={infoU:.8f}, certified finite lower={info_lower:.8f}")
    print(f"  V_F and K_G singleton lower={vf_lower:.8f}, V_U finite lower={vu_lower:.8f}")
    print(f"  verified D>X atoms={atom_checks}")
    print(f"  reflection-quotient singletons={quotient_checks}, TV sum={tvF:.8f}, lower={tv_lower:.8f}")


def blocked_state_test(X):
    primes, lpf, _ = sieve(X + 1)
    trunc = [1] * (X + 2)
    # Exponents 0.89, 0.90, 0.95; integer comparisons avoid root rounding.
    B = [n for n in range(1, X + 1)
         if lpf[n] ** 2 > X + 1 and lpf[n + 1] ** 2 > X + 1
         and lpf[n] ** 100 <= X ** 89 and lpf[n + 1] ** 100 <= X ** 89]
    energy = lower = harmonic = 0.0
    for p in primes:
        if p ** 20 > X ** 19:
            break
        if p ** 10 > X ** 9:
            H = [int(n % p == 0 or (n + 1) % p == 0) for n in range(1, X + 1)]
            state_groups = defaultdict(list)
            for n in range(1, X + 1):
                pair = tuple(sorted((trunc[n], trunc[n + 1])))
                state_groups[pair].append(n - 1)
            for g in state_groups.values():
                v = sum(H[i] for i in g) / len(g)
                energy += p * len(g) / X * (v - 2 / p) ** 2
            for n in B:
                assert trunc[n] == lpf[n] and trunc[n + 1] == lpf[n + 1]
                assert H[n - 1] == 0
                pair = tuple(sorted((trunc[n], trunc[n + 1])))
                assert all(H[i] == 0 for i in state_groups[pair])
            harmonic += 1 / p
            lower += 4 * len(B) / (X * p)
        for m in range(p, X + 2, p):
            trunc[m] = p
    assert energy + 1e-10 >= lower
    assert abs(lower - 4 * len(B) / X * harmonic) < 1e-10
    print(f"blocked-state X={X}: mass={len(B)/X:.8f}, V_W={energy:.8f}, lower={lower:.8f}")


if __name__ == '__main__':
    checks = sum(exact_identities(X) for X in range(1, 251))
    print(f"PASS exact recursions, weights, |u|<=5, and cofactor identities for X=1..250 ({checks} cofactor checks)")
    divisor_moment_test()
    for X in (200, 1000, 5000):
        filtration_test(X)
    blocked_state_test(5000)
    b, c = 3 / 4, 9 / 10
    kappa = log(c * c / b)
    delta = 2 * log(2 * .89) - 1
    print(f"asymptotic constants: kappa=log(27/25)={kappa:.12f}, b*kappa={b*kappa:.12f}")
    print(f"blocked-state constants: delta={delta:.12f}, 4*delta*log(19/18)={4*delta*log(19/18):.12f}")
    print('PASS all finite checks (not a numerical proof of an asymptotic claim).')
