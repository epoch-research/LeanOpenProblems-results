#!/usr/bin/env python3
"""Exact finite regression checks for DirectOddCountResearch.md.

No numerical asymptotic experiment is performed. All arithmetic is integer,
rational, or in Q[zeta_n] = Q[x]/Phi_n(x). The continuous analytic assertions
are proved in the note, not certified by these finite checks. No project files
(in particular no Spec file) are read. No third-party package is required.
"""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import gcd, isqrt


ASSERTIONS = 0


def require(condition, description):
    global ASSERTIONS
    ASSERTIONS += 1
    if not condition:
        raise AssertionError(description)


def trim(poly):
    poly = list(poly)
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return tuple(poly) if poly else (0,)


def poly_mul(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                if b:
                    out[i + j] += a * b
    return trim(out)


def poly_divmod_monic(numerator, denominator):
    if denominator[-1] != 1:
        raise ValueError("The divisor must be monic")
    remainder = list(trim(numerator))
    quotient = [0] * max(1, len(remainder) - len(denominator) + 1)
    while trim(remainder) != (0,) and len(remainder) >= len(denominator):
        shift = len(remainder) - len(denominator)
        coeff = remainder[-1]
        quotient[shift] += coeff
        for j, value in enumerate(denominator):
            remainder[shift + j] -= coeff * value
        remainder = list(trim(remainder))
    return trim(quotient), trim(remainder)


@lru_cache(maxsize=None)
def cyclotomic(n):
    if n < 1:
        raise ValueError("Cyclotomic order must be positive")
    result = (-1,) + (0,) * (n - 1) + (1,)
    for d in range(1, n):
        if n % d == 0:
            result, remainder = poly_divmod_monic(result, cyclotomic(d))
            if remainder != (0,):
                raise AssertionError("Nonexact cyclotomic division")
    return result


class CyclotomicField:
    """Small exact polynomial quotient; coefficients may be Fractions."""

    def __init__(self, order):
        self.order = order
        self.modulus = cyclotomic(order)
        self.zero = (0,)
        self.one = (1,)

    def reduce(self, poly):
        return poly_divmod_monic(trim(poly), self.modulus)[1]

    def constant(self, value):
        return trim((value,))

    def add(self, left, right):
        out = [0] * max(len(left), len(right))
        for i, value in enumerate(left):
            out[i] += value
        for i, value in enumerate(right):
            out[i] += value
        return trim(out)

    def scale(self, scalar, value):
        return trim(tuple(scalar * x for x in value))

    def sub(self, left, right):
        return self.add(left, self.scale(-1, right))

    def mul(self, left, right):
        return self.reduce(poly_mul(left, right))

    @lru_cache(maxsize=None)
    def root(self, exponent):
        exponent %= self.order
        return self.reduce((0,) * exponent + (1,))

    def terms(self, terms):
        out = [0] * self.order
        for exponent, coeff in terms:
            out[exponent % self.order] += coeff
        return self.reduce(out)

    def conjugate(self, value):
        return self.terms((-i, coeff) for i, coeff in enumerate(value))

    def norm_square(self, value):
        return self.mul(value, self.conjugate(value))

    def sum(self, values):
        out = self.zero
        for value in values:
            out = self.add(out, value)
        return out


def primes_up_to(limit):
    return [n for n in range(2, limit + 1)
            if all(n % d for d in range(2, isqrt(n) + 1))]


PRIMES = (3, 5, 7, 11, 13, 17, 19, 23)


def discrete_logs(p):
    for generator in range(2, p):
        residues = [pow(generator, k, p) for k in range(p - 1)]
        if len(set(residues)) == p - 1:
            return {residue: k for k, residue in enumerate(residues)}
    raise AssertionError("No primitive root found for a tested prime")


def character(field, p, logs, j, value):
    residue = value % p
    return field.zero if residue == 0 else field.root(j * logs[residue])


def check_cyclotomic_arithmetic():
    known = {
        1: (-1, 1), 2: (1, 1), 3: (1, 1, 1),
        4: (1, 0, 1), 5: (1, 1, 1, 1, 1),
        6: (1, -1, 1), 8: (1, 0, 0, 0, 1),
        12: (1, 0, -1, 0, 1),
    }
    for n, expected in known.items():
        require(cyclotomic(n) == expected, f"Phi_{n}")
    for n in range(1, 41):
        product = (1,)
        for d in range(1, n + 1):
            if n % d == 0:
                product = poly_mul(product, cyclotomic(d))
        require(product == (-1,) + (0,) * (n - 1) + (1,),
                f"Cyclotomic factorization at n={n}")
        field = CyclotomicField(n)
        for exponent in range(n):
            require(field.mul(field.root(exponent), field.root(-exponent))
                    == field.one, "Root-of-unity inversion")
            require(field.conjugate(field.root(exponent)) == field.root(-exponent),
                    "Exact conjugation")


def check_character_coefficients():
    u_plus = Fraction(3, 7)
    u_minus = Fraction(2, 5)
    for p in PRIMES:
        field = CyclotomicField(p - 1)
        logs = discrete_logs(p)
        for value in range(p):
            minus_residue = int(value == p - 1)
            plus_residue = int(value == 1)
            odd_sum = field.sum(character(field, p, logs, j, value)
                                for j in range(1, p - 1, 2))
            require(field.scale(-2, odd_sum)
                    == field.constant((p - 1) * (minus_residue - plus_residue)),
                    f"Negative centered odd coefficient, p={p}, value={value}")
            exact_sum = field.sum(
                field.scale(((-1) ** j) * u_plus - u_minus,
                            character(field, p, logs, j, value))
                for j in range(p - 1))
            require(exact_sum == field.constant((p - 1) *
                    (u_plus * minus_residue - u_minus * plus_residue)),
                    "Exact shifted character coefficient, including even terms")
        for j in range(p - 1):
            is_real = all(character(field, p, logs, j, value)
                          == field.conjugate(character(field, p, logs, j, value))
                          for value in range(1, p))
            require(is_real == (j in (0, (p - 1) // 2)),
                    "Only principal and quadratic characters are real")
            require(character(field, p, logs, j, p - 1)
                    == field.constant((-1) ** j), "Odd character parity")
        quadratic_index = (p - 1) // 2
        require((quadratic_index % 2 == 1) == (p % 4 == 3),
                "Quadratic is odd exactly for p=3 mod 4")
        for value in range(1, p):
            euler = pow(value, quadratic_index, p)
            legendre = -1 if euler == p - 1 else euler
            require(character(field, p, logs, quadratic_index, value)
                    == field.constant(legendre), "Quadratic equals Legendre")


def check_odd_parseval_and_inverse_projection():
    for p in PRIMES:
        field = CyclotomicField(p - 1)
        logs = discrete_logs(p)
        beta = {n: (n * n + 3 * n + 1) % 11 - 5 for n in range(1, 3 * p + 4)}
        residue_sums = [0] * p
        for n, value in beta.items():
            if n % p:
                residue_sums[n % p] += value
        lhs = (p - 1) * sum((residue_sums[a] - residue_sums[-a % p]) ** 2
                            for a in range(1, p))
        moment = field.zero
        for j in range(1, p - 1, 2):
            b_chi = field.sum(field.scale(value, character(field, p, logs, j, n))
                              for n, value in beta.items())
            moment = field.add(moment, field.norm_square(b_chi))
        require(field.constant(lhs) == field.scale(4, moment),
                "Odd Parseval: (p-1) sum|T(a)-T(-a)|^2 = 4 sum_odd |B_chi|^2")

        additive = CyclotomicField(p)
        for h in range(p + 2):
            lhs = additive.sum(
                additive.scale(value, additive.sub(
                    additive.root(h * pow(n, -1, p)),
                    additive.root(-h * pow(n, -1, p))))
                for n, value in beta.items() if n % p)
            rhs = additive.terms(
                (h * x, residue_sums[pow(x, -1, p)]
                 - residue_sums[-pow(x, -1, p) % p])
                for x in range(1, p))
            require(lhs == rhs, "Inverse-residue odd projection before division by 2i")
            if h == 0:
                require(lhs == additive.zero, "Zero sine frequency vanishes")


def check_gauss_identities():
    for p in (3, 5, 7, 11, 13):
        n = p - 1
        field = CyclotomicField(p * n)
        logs = discrete_logs(p)
        # zeta_n = zeta_(pn)^p; zeta_p = zeta_(pn)^n.
        for j in range(1, n):
            tau = field.terms((p * j * logs[a] + n * a, 1) for a in range(1, p))
            tau_bar_character = field.terms((-p * j * logs[a] + n * a, 1)
                                             for a in range(1, p))
            require(field.norm_square(tau) == field.constant(p),
                    "Nonprincipal prime Gauss norm is p")
            for value in range(p):
                lhs = field.terms((-p * j * logs[a] + n * value * a, 1)
                                  for a in range(1, p))
                chi_value = (field.zero if value == 0
                             else field.root(p * j * logs[value]))
                require(lhs == field.mul(chi_value, tau_bar_character),
                        "Finite Fourier expansion using tau(conjugate chi)")


def check_fourier_positive_four():
    for p in PRIMES:
        field = CyclotomicField(p)
        sequence = {m: (m * m + 5 * m + 2) % 13 - 6
                    for m in range(-2 * p, 3 * p + 1)}
        residue_sums = [0] * p
        for m, value in sequence.items():
            residue_sums[m % p] += value
        transform = [field.terms((-h * m, value) for m, value in sequence.items())
                     for h in range(p)]
        require(transform[0] == field.constant(sum(sequence.values())),
                "Unnormalized discrete Fourier transform at zero")
        for h in range(1, p):
            require(transform[-h % p] == field.conjugate(transform[h]),
                    "Fourier reality symmetry")
        require(any(residue_sums[-x % p] != residue_sums[x] for x in range(1, p)),
                "Fourier sign fixture is nonzero")
        for x in range(1, p):
            expected = field.constant(p * (residue_sums[-x % p] - residue_sums[x]))
            unpaired = field.sum(field.mul(transform[h], field.sub(
                field.root(-h * x), field.root(h * x))) for h in range(p))
            require(unpaired == expected, "Residue Poisson/DFT sign and 1/p")
            # 4 Im(F_h) sin(theta) = -(F_h-conj(F_h))*(e(theta)-e(-theta)).
            paired = field.sum(field.scale(-1, field.mul(
                field.sub(transform[h], transform[-h % p]),
                field.sub(field.root(h * x), field.root(-h * x))))
                for h in range(1, (p - 1) // 2 + 1))
            require(paired == expected, "Positive-four Fourier pairing")


def jacobi(a, n):
    if n <= 0 or n % 2 == 0:
        raise ValueError("Jacobi denominator must be positive and odd")
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0


def squarefree_part(n):
    out = 1
    divisor = 2
    while divisor * divisor <= n:
        parity = 0
        while n % divisor == 0:
            n //= divisor
            parity ^= 1
        if parity:
            out *= divisor
        divisor += 1
    return out * n


def check_jacobi_and_square_pairs():
    for p in PRIMES:
        for value in range(2 * p):
            euler = pow(value, (p - 1) // 2, p)
            legendre = -1 if euler == p - 1 else euler
            require(jacobi(value, p) == legendre, "Jacobi agrees with Legendre on primes")
    for numerator in range(1, 97):
        period = 8 * numerator
        complete = 0
        for r in range(1, period, 2):
            value = jacobi(numerator, r)
            complete += value
            require(value == jacobi(numerator, r + period), "Jacobi 8n periodicity")
            if isqrt(numerator) ** 2 == numerator:
                require(value == int(gcd(numerator, r) == 1), "Square Jacobi numerator")
        if isqrt(numerator) ** 2 != numerator:
            require(complete == 0, "Nonsquare complete Jacobi period has mean zero")
    for b in range(1, 14):
        for b_prime in range(1, 14):
            for r in range(1, 40, 2):
                require(jacobi(b * b_prime, r) == jacobi(b, r) * jacobi(b_prime, r),
                        "Jacobi multiplicativity used in the second moment")
    for B in range(1, 21):
        values = range(B, 2 * B + 1)
        counts = Counter(squarefree_part(value) for value in values)
        pairs = 0
        for b in values:
            for b_prime in values:
                is_square = isqrt(b * b_prime) ** 2 == b * b_prime
                require(is_square == (squarefree_part(b) == squarefree_part(b_prime)),
                        "Square-pair parametrization by the same squarefree part")
                pairs += is_square
        require(pairs == sum(count * count for count in counts.values()),
                "Square-pair count decomposition")


def rational_bump(x):
    """A rational finite fixture only; no smooth analytic estimate uses it."""
    return (x - 1) ** 2 * (2 - x) ** 2 if 1 < x < 2 else Fraction(0)


def check_circle_and_centering_identities():
    a_weights = {2: 1, 3: -2, 4: 3, 5: 2}
    b_weights = {1: 2, 2: -1, 3: 4}
    p_weights = {3: 2, 5: 3, 7: 5}
    q_weights = {5: 7, 7: 11, 11: 13}
    f_coeffs, g_coeffs = Counter(), Counter()
    for a, ua in a_weights.items():
        for p, wp in p_weights.items():
            f_coeffs[a * p] += ua * wp
    for b, vb in b_weights.items():
        for q, zq in q_weights.items():
            g_coeffs[b * q] += vb * zq
    product = Counter()
    for m, value in f_coeffs.items():
        for n, other in g_coeffs.items():
            product[m - n] += value * other
    direct = sum(ua * vb * wp * zq *
                 (int(a * p - b * q == 1) - int(a * p - b * q == -1))
                 for a, ua in a_weights.items() for b, vb in b_weights.items()
                 for p, wp in p_weights.items() for q, zq in q_weights.items())
    constant_after_multiplier = product[1] - product[-1]
    require(direct == constant_after_multiplier,
            "Circle identity: e(-alpha)-e(alpha) = -2i sin(2 pi alpha)")
    require(direct != 0, "Circle sign fixture is nonzero")

    A = 5
    b_values, p_values, q_values = range(1, 6), (3, 5, 7), (11, 13, 17, 19, 23)
    direct = Fraction(0)
    eliminated = Fraction(0)
    centered = Fraction(0)
    for b in b_values:
        for p in p_values:
            for q in q_values:
                weight = (b + 1) * (p + 2) * (q + 3)
                for a in range(1, 2 * A + 1):
                    direct += weight * rational_bump(Fraction(a, A)) * (
                        int(a * p - b * q == 1) - int(a * p - b * q == -1))
                plus_indicator = int((b * q + 1) % p == 0)
                minus_indicator = int((b * q - 1) % p == 0)
                eliminated += weight * (
                    rational_bump(Fraction(b * q + 1, p * A)) * plus_indicator
                    - rational_bump(Fraction(b * q - 1, p * A)) * minus_indicator)
                centered += weight * rational_bump(Fraction(b * q, p * A)) * (
                    plus_indicator - minus_indicator)
    require(direct == eliminated, "Exact elimination of a includes both shifted U values")
    require(direct != centered, "Centering is not an exact identity for D")


def distance_to_integer(value):
    fractional = value - (value.numerator // value.denominator)
    return min(fractional, 1 - fractional)


def check_rational_geometry():
    for P in (7, 11, 17):
        moduli = [p for p in primes_up_to(2 * P - 1) if p > P]
        points = sorted(Fraction(a, p) for p in moduli for a in range(1, p))
        gaps = [right - left for left, right in zip(points, points[1:])]
        gaps.append(1 + points[0] - points[-1])
        require(min(gaps) >= Fraction(1, 4 * P * P), "Reduced-fraction separation")
        for p in moduli:
            for r in range(2, min(P, 8)):
                for c in range(1, r):
                    if gcd(c, r) != 1:
                        continue
                    require(distance_to_integer(Fraction(c * p, r)) >= Fraction(1, r),
                            "Noncentral rational distance before perturbation")
                    for sign in (-1, 1):
                        alpha = Fraction(c, r) + sign * Fraction(1, 8 * r * P)
                        require(distance_to_integer(alpha * p) >= Fraction(3, 4 * r),
                                "Exact finite checks of the 3/(4r) arc constant")
            for sign in (-1, 1):
                require(abs(Fraction(sign * p, 8 * P)) <= Fraction(1, 4),
                        "Central arc gives |alpha p| <= 1/4")
    require(gcd(1, 1) == 1 and 1 != 0
            and distance_to_integer(Fraction(1 * 11, 1)) < Fraction(3, 4),
            "c=r=1 is a counterexample if only c!=0 is specified")


def check_exponents():
    A, B, P, Q, H = (Fraction(2, 5), Fraction(1, 10), Fraction(3, 5),
                     Fraction(9, 10), Fraction(1, 2))
    identities = {
        "AP=X": (A + P, Fraction(1)),
        "BQ=X": (B + Q, Fraction(1)),
        "P/B=H": (P - B, H),
        "AB=H": (A + B, H),
        "centering BQ/(AP)": (B + Q - A - P, Fraction(0)),
        "PB": (P + B, Fraction(7, 10)),
        "B^4": (4 * B, Fraction(2, 5)),
        "real odd main": (Q + B / 2, Fraction(19, 20)),
        "real odd secondary": (Q + 2 * B - P / 2, Fraction(4, 5)),
        "real odd symmetric shift error": (B + Q - 2 * A - 2 * P, Fraction(-1)),
        "P^3 Q": (3 * P + Q, Fraction(27, 10)),
        "low-frequency prefactor": (Fraction(3, 2) * P + Q / 2 - 2 * H,
                                     Fraction(7, 20)),
        "R=X^(2/5)": (Fraction(3, 2) * P + Q / 2 - 2 * H
                       + Fraction(3, 2) * Fraction(2, 5), Fraction(19, 20)),
        "R=H is not a saving": (Fraction(3, 2) * P + Q / 2 - H / 2,
                                Fraction(11, 10)),
    }
    for description, (actual, expected) in identities.items():
        require(actual == expected, description)
    require(2 * P > Q and 2 * P > H, "P^2 dominates Q and H")
    require(P + B > 4 * B, "PB dominates B^4 at these scales")
    require(Q > P > A > B, "Ordering of prime and cofactor scales")
    for J in range(3, 11):
        require(2 - 2 * P - J * A == (2 - J) * A,
                "Central alias error X^2 P^-2 A^-J = A^(2-J)")
        require((2 - J) * A < 0, "Central alias term decays for J>2")


def fundamental_character(D, r):
    """Positive fundamental-discriminant Kronecker character on r>=1."""
    twos = 0
    while r % 2 == 0:
        r //= 2
        twos += 1
    if twos and D % 2 == 0:
        return 0
    at_two = 1 if D % 8 in (1, 7) else -1
    return (at_two ** twos) * jacobi(D, r)


def squarefree_divisors_with_mobius(n):
    out = [(1, 1)]
    p = 2
    while p * p <= n:
        if n % p == 0:
            out += [(d * p, -mu) for d, mu in list(out)]
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out += [(d * n, -mu) for d, mu in list(out)]
    return out


def check_stronger_completion_and_exponents():
    for n in range(2, 401):
        d = squarefree_part(n)
        if d == 1:
            continue
        s = isqrt(n // d)
        D = d if d % 4 == 1 else 4 * d
        divisors = squarefree_divisors_with_mobius(2 * s)
        require(n == d * s * s and D <= 4 * d, "Fundamental conductor size")
        require(len(divisors) <= 2 * s, "Number of primitive completion terms")
        for r in range(1, 301):
            lhs = jacobi(n, r) if r % 2 else 0
            rhs = fundamental_character(D, r) * int(gcd(r, 2 * s) == 1)
            require(lhs == rhs, "Imprimitive Jacobi character including square-part zeros")
            mobius = sum(mu * fundamental_character(D, e) *
                         fundamental_character(D, r // e)
                         for e, mu in divisors if r % e == 0)
            require(lhs == mobius, "Exact Mobius reduction to primitive interval sums")
    for i in range(51, 100):
        for j in range(i, 100):
            a, b = Fraction(i, 100), Fraction(j, 100)
            B = 1 - b
            first = b + B / 2
            second = b + 3 * B / 2 - a / 2
            require(first == (1 + b) / 2, "General first real-character exponent")
            require(second == (3 - a - b) / 2, "General second real-character exponent")
            require(max(first, second) < 1, "Strict saving in interior high-factor region")
    a, b, h, R = Fraction(3, 5), Fraction(9, 10), Fraction(1, 2), Fraction(2, 5)
    require(b + 3 * (1-b) / 2 - a / 2 == Fraction(3, 4), "Improved pilot second exponent")
    require(a + b / 2 + 2 * R - 2 * h == Fraction(17, 20),
            "Proper-prime-power low-frequency error exponent")
    require(1-b + b/2 == Fraction(11, 20), "Direct q-prime-power replacement exponent")



def check_critical_kernel_arithmetic():
    """Finite algebra behind section 12; no analytic bound is tested."""
    primes = primes_up_to(200)
    for p in primes:
        for q in range(2, 81):
            if q % p == 0:
                continue
            x = pow(q, -1, p)
            for b in range(-2*p, 2*p + 1):
                selected = (b*q - 1) % p == 0
                j = (x-b) // p
                require(selected == (b == x-j*p),
                        "Exact inverse-residue parametrization, both signs")
                if selected:
                    require(b != 0, "Inverse-residue integer is nonzero")
    for q in range(2, 101):
        for b in range(-30, 31):
            if b == 0:
                continue
            n = abs(b*q - 1)
            product = 1
            for p in primes:
                if n % p == 0:
                    product *= p
            require(n != 0 and n % product == 0 and product <= n,
                    "Distinct-prime product divisor inequality")

    def factors(n):
        out = {}
        p = 2
        while p*p <= n:
            while n % p == 0:
                out[p] = out.get(p, 0) + 1
                n //= p
            p += 1
        if n > 1:
            out[n] = out.get(n, 0) + 1
        return out

    def squarefull_part(n):
        out = 1
        for p, e in factors(n).items():
            if e >= 2:
                out *= p**e
        return out

    def mu(n):
        f = factors(n)
        return 0 if any(e > 1 for e in f.values()) else (-1)**len(f)

    for d in range(1, 151):
        if mu(d) == 0:
            continue
        for v in range(1, 181):
            s = squarefull_part(v)
            t = v // s
            gs, gt = gcd(d, s), gcd(d, t)
            d0, v0, delta = d // (gs*gt), t // gt, s*gs*gt*gt
            require(gs*gt == gcd(d, v), "Disjoint common factors")
            require(d0*v0*delta == d*v, "Exact exceptional-pair factorization")
            require(gcd(d0, v0) == gcd(d0, delta) == gcd(v0, delta) == 1,
                    "Three remaining factors are pairwise coprime")
            require(mu(d0) != 0 and mu(v0) != 0,
                    "Remaining large factors are squarefree")
            require(delta == squarefull_part(d*v),
                    "Delta is exactly the squarefull part of the product")
            require(delta <= s*gcd(d, v)**2,
                    "Small squarefull-factor upper bound")
            require(mu(d) == mu(d0)*mu(gs)*mu(gt),
                    "Actual Mobius coefficient factorization")
            require(v == s*gt*v0, "Actual b_z coefficient argument")
    P, Q, H = Fraction(3, 5), Fraction(9, 10), Fraction(1, 2)
    require(P + Q - 2*H == Fraction(1, 2),
            "Full-block critical bound equals X^(1/2) T up to logs")
    require(P + Q - H == 1, "Main smooth band is critical, not saving")
    eta = Fraction(1, 100)
    require(2*eta + 2*eta == 4*eta, "Delta small-factor exponent")
    require(Fraction(9, 20) - 2*eta - eta == Fraction(9, 20) - 3*eta,
            "Second large-factor lower exponent")

def main():
    groups = (
        ("exact cyclotomic arithmetic", check_cyclotomic_arithmetic),
        ("character coefficients and real-odd parity", check_character_coefficients),
        ("odd Parseval and inverse-residue projection", check_odd_parseval_and_inverse_projection),
        ("prime Gauss sums", check_gauss_identities),
        ("positive-four Fourier pairing", check_fourier_positive_four),
        ("Jacobi periods and square-pair identities", check_jacobi_and_square_pairs),
        ("circle sign and exact versus centered weights", check_circle_and_centering_identities),
        ("rational arc constants and integer-center exception", check_rational_geometry),
        ("scale and exponent identities", check_exponents),
        ("primitive completion and high-factor exponents", check_stronger_completion_and_exponents),
        ("critical-kernel arithmetic and exceptional factorization", check_critical_kernel_arithmetic),
    )
    for name, test in groups:
        before = ASSERTIONS
        test()
        print(f"PASS {name}: {ASSERTIONS - before} exact assertions")
    print(f"PASS all {len(groups)} groups: {ASSERTIONS} exact assertions")
    print("Exponents: real odd=19/20; low prefactor=7/20; "
          "low at R=X^(2/5)=19/20; low at R=H=11/10.")
    print("Scope: finite identities/exponents only; no numerical asymptotic evidence, "
          "no verification of the target theorem.")


if __name__ == "__main__":
    main()
