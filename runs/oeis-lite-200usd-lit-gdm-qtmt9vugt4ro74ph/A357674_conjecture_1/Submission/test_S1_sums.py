from fractions import Fraction

def test_S1(p):
    S1_1 = sum(Fraction(1, k) for k in range(1, p))
    S1_2 = sum(Fraction(sum(Fraction(1, i) for i in range(1, k)), k) for k in range(1, p))
    S1_3 = sum(Fraction(sum(Fraction(1, i) for i in range(1, k))**2 - sum(Fraction(1, i**2) for i in range(1, k)), k) for k in range(1, p))
    S1_4 = sum(Fraction(sum(Fraction(1, i) for i in range(1, k))**3 - 3 * sum(Fraction(1, i) for i in range(1, k)) * sum(Fraction(1, i**2) for i in range(1, k)) + 2 * sum(Fraction(1, i**3) for i in range(1, k)), k) for k in range(1, p))
    
    print(f"p = {p}:")
    print(f"  sum 1/k = {S1_1} (val mod p^4 = {S1_1.numerator * pow(S1_1.denominator, -1, p**4) % p**4 if S1_1 != 0 else 0})")
    print(f"  sum H/k = {S1_2} (val mod p^3 = {S1_2.numerator * pow(S1_2.denominator, -1, p**3) % p**3 if S1_2 != 0 else 0})")
    print(f"  sum (H^2-H2)/k = {S1_3} (val mod p^2 = {S1_3.numerator * pow(S1_3.denominator, -1, p**2) % p**2 if S1_3 != 0 else 0})")
    print(f"  sum (H^3-3HH2+2H3)/k = {S1_4} (val mod p = {S1_4.numerator * pow(S1_4.denominator, -1, p) % p if S1_4 != 0 else 0})")

test_S1(5)
test_S1(7)
