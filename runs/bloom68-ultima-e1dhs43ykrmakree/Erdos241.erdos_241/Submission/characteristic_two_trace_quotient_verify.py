"""Independent stdlib-only check of the Sage audit's saved certificates.

Run: python3 Submission/characteristic_two_trace_quotient_verify.py
Uses binary-polynomial field arithmetic, not Sage or its generated code.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json


class BinaryField:
    def __init__(self, modulus):
        self.modulus = 0
        for term in modulus.split(' + '):
            exponent = int(term.split('^')[1]) if '^' in term else (1 if term == 'x' else 0)
            self.modulus ^= 1 << exponent
        self.degree = self.modulus.bit_length() - 1

    def mul(self, a, b):
        answer = 0
        while b:
            if b & 1:
                answer ^= a
            b >>= 1
            a <<= 1
            if a >> self.degree:
                a ^= self.modulus
        return answer

    def power(self, a, n):
        answer = 1
        while n:
            if n & 1:
                answer = self.mul(answer, a)
            a = self.mul(a, a)
            n >>= 1
        return answer

    def trace(self, a, k):
        answer = 0
        for _ in range(k):
            answer ^= a
            a = self.mul(a, a)
        return answer

    def pmul(self, a, b):
        answer = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                answer[i+j] ^= self.mul(x, y)
        return answer

    def remainder(self, a, f):
        assert f[-1] == 1
        answer = a[:]
        for i in range(len(answer)-1, len(f)-2, -1):
            leading = answer[i]
            for j, c in enumerate(f):
                answer[i-len(f)+1+j] ^= self.mul(leading, c)
        return (answer + [0]*len(f))[:len(f)-1]

    def evaluate(self, p, x):
        answer = 0
        for a in reversed(p):
            answer = self.mul(answer, x) ^ a
        return answer

    def cubic(self, roots):
        answer = [1]
        for t in roots:
            answer = self.pmul(answer, [t, 1])
        return answer


def verify_certificate(field, theta, q, h, trace_bit, certificate):
    left = certificate['left_parameters']
    right = certificate['right_parameters']
    assert len(left) == len(right) == 3
    k = q.bit_length()-1
    assert field.power(theta, q) != theta
    for t in left + right:
        assert field.power(t, q) == t
        assert field.trace(t, k) == trace_bit
    f = certificate['f_coefficients_ascending']
    g = certificate['zeta_quadratic_coefficients_ascending']
    zeta = certificate['zeta']
    assert field.evaluate(f, theta) == 0
    assert all(field.power(a, q) == a for a in f)
    assert field.evaluate(g, theta) == zeta
    assert zeta != 1 and field.power(zeta, h) == 1
    P, Q = field.cubic(left), field.cubic(right)
    assert P != Q
    assert field.evaluate(P, theta) == field.mul(zeta, field.evaluate(Q, theta))
    residue = field.remainder(field.pmul(g, [x ^ y for x, y in zip(Q, f)]), f)
    assert [f[i] ^ (residue[i] if i < 3 else 0) for i in range(4)] == P
    columns = [field.remainder([0]*j + g, f) for j in range(3)]
    matrix = certificate['multiplication_matrix_ascending_basis']
    assert matrix == [[columns[j][i] for j in range(3)] for i in range(3)]
    assert matrix[2][0] or matrix[2][1]
    left_classes = sorted(field.power(theta ^ t, h) for t in left)
    right_classes = sorted(field.power(theta ^ t, h) for t in right)
    assert left_classes != right_classes


def strong_b3(values, M):
    seen = set()
    for triple in combinations_with_replacement(values, 3):
        residue = sum(triple) % M
        if residue in seen:
            return False
        seen.add(residue)
    return True


def main():
    path = Path('Submission/characteristic_two_trace_quotient_results.json')
    data = json.loads(path.read_text())
    small = data['q16_exhaustive']
    field = BinaryField(small['field_modulus'])
    histogram = Counter()
    for record in small['records']:
        theta = record['theta']
        values = record['quotient_logarithms']
        for a, t in zip(values, record['parameters_for_logarithms']):
            assert field.power(field.power(small['primitive_generator'], a), 13) == field.power(theta ^ t, 13)
        maximum = max(n for n in range(len(values)+1)
                      if any(strong_b3(subset, 315) for subset in combinations(values, n)))
        assert maximum == record['maximum_strong_B3_subset_size']
        assert set(record['maximizer_logarithms']) <= set(values)
        assert strong_b3(record['maximizer_logarithms'], 315)
        assert not strong_b3(values, 315)
        histogram[maximum] += record['orbit_size']
        verify_certificate(field, theta, 16, 13, 0, record['polynomial_certificate'])
    assert histogram == {6: 3000, 5: 1032, 4: 48}
    assert sum(histogram.values()) == 4080
    large = data['q256_fixed_field_diagnostic']
    field = BinaryField(large['field_modulus'])
    for certificate in large['witnesses'].values():
        verify_certificate(field, large['theta'], 256, 13, 1, certificate)
    hist = {int(m): n for m, n in large['triple_product_multiplicity_histogram'].items()}
    assert sum(hist.values()) == 314546
    assert sum(m*n for m, n in hist.items()) == 357760
    assert sum(m*(m-1)//2*n for m, n in hist.items()) == 46732
    assert 13*Fraction(5, 12)**3 == Fraction(1625, 1728) < 1
    assert 7*Fraction(25, 48)**3 == Fraction(109375, 110592) < 1
    print('Verified independently: all 46 q=16 maxima, all 49 polynomial certificates,')
    print('the q=256 multiplicity totals, and both strict cubic-ratio bounds.')


if __name__ == '__main__':
    main()
