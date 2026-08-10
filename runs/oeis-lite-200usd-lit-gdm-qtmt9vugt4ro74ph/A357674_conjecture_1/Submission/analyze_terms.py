def choose(n, k):
    import math
    return math.comb(n, k)

def test(p):
    p5 = p**5
    # S1 terms
    S1_0 = choose(p - 1, 0)
    S1_mid1 = sum(choose(p + k - 1, k) for k in range(1, p))
    S1_p = choose(2 * p - 1, p)
    S1_mid2 = sum(choose(p + k - 1, k) for k in range(p + 1, 2 * p))
    S1_2p = choose(3 * p - 1, 2 * p)
    
    # S2 terms
    S2_0 = choose(p - 1, 0)**2
    S2_mid1 = sum(choose(p + k - 1, k)**2 for k in range(1, p))
    S2_p = choose(2 * p - 1, p)**2
    S2_mid2 = sum(choose(p + k - 1, k)**2 for k in range(p + 1, 2 * p))
    S2_2p = choose(3 * p - 1, 2 * p)**2
    
    print(f"p = {p}")
    print(f"  S1: 0={S1_0}, mid1={S1_mid1 % p5}, p={S1_p % p5}, mid2={S1_mid2 % p5}, 2p={S1_2p % p5}")
    print(f"  S2: 0={S2_0}, mid1={S2_mid1 % p5}, p={S2_p % p5}, mid2={S2_mid2 % p5}, 2p={S2_2p % p5}")
    
    total = 3 * (S2_0 + S2_mid1 + S2_p + S2_mid2 + S2_2p) + 4 * (S1_0 + S1_mid1 + S1_p + S1_mid2 + S1_2p)
    print(f"  Total mod p^5 = {total % p5}")

test(5)
test(7)
