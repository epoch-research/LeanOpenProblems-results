import math

def choose(n, k):
    return math.comb(n, k)

def test_p(p):
    p5 = p**5
    print(f"p = {p}:")
    for k in range(1, p):
        # Uk
        term1 = choose(p + k - 1, k)
        Uk = (3 * term1**2 + 4 * term1) % p5
        
        # U_{2p-k}
        term2 = choose(p + (2*p-k) - 1, 2*p-k)
        U_alt = (3 * term2**2 + 4 * term2) % p5
        
        sum_U = (Uk + U_alt) % p5
        print(f"  k = {k}: sum_U = {sum_U}")

test_p(5)
