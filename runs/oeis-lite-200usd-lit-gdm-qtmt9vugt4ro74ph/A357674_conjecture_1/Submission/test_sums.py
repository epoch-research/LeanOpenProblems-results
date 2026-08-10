def H(n, exp=1):
    return sum(1 / (i**exp) for i in range(1, n + 1))

def test_p(p):
    # compute with fractions
    from fractions import Fraction
    S_2_1 = sum(Fraction(1, k**2) for k in range(1, p))
    S_2_2 = sum(Fraction(sum(Fraction(1, i) for i in range(1, k)), k**2) for k in range(1, p))
    S_2_3 = sum(Fraction(2 * sum(Fraction(1, i) for i in range(1, k))**2 - sum(Fraction(1, i**2) for i in range(1, k)), k**2) for k in range(1, p))
    
    print(f"p = {p}:")
    print(f"  sum 1/k^2 = {S_2_1} (val mod p^3 = {S_2_1.numerator * pow(S_2_1.denominator, -1, p**3) % p**3})")
    print(f"  sum H_{{k-1}}/k^2 = {S_2_2} (val mod p^2 = {S_2_2.numerator * pow(S_2_2.denominator, -1, p**2) % p**2})")
    print(f"  sum (2H^2-H2)/k^2 = {S_2_3} (val mod p = {S_2_3.numerator * pow(S_2_3.denominator, -1, p) % p})")

test_p(5)
test_p(7)
