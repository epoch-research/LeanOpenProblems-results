def choose(n, k):
    import math
    return math.comb(n, k)

def test_U(p):
    p5 = p**5
    print(f"p = {p}:")
    total = 0
    for k in range(2 * p + 1):
        term1 = choose(p + k - 1, k)
        val1 = term1 % p5
        val2 = (term1**2) % p5
        Uk = (3 * val2 + 4 * val1) % p5
        total = (total + Uk) % p5
        print(f"  k = {k:2d}: term = {val1:5d}, term^2 = {val2:5d}, Uk = {Uk:5d}")
    print(f"  Total mod p^5 = {total}")

test_U(5)
test_U(7)
