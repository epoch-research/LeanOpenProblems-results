def vp_F_mod(n, p, max_v):
    # We want F(n) / n! = sum_{k=2}^n (-1)^k / k mod p^max_v
    # Actually, F(n) = n! * S_n
    # v_p(F(n)) = v_p(n!) + v_p(S_n)
    # So v_p(A(n)) = min(v_p(n!), v_p(n!) + v_p(S_n)) = v_p(n!) + min(0, v_p(S_n))
    # We just need to find v_p(S_n).
    
    # S_n is a rational number. We can compute it modulo p^K.
    pass

def check_prime(p):
    # S_{p^2} = sum_{k=2}^{p^2} (-1)^k / k
    # We want v_p(S_{p^2}) and v_p(S_{p^2-1}).
    # Note that S_{p^2} = S_{p^2-1} + 1/p^2  (since p^2 is odd for p>2? No, p^2 is odd, so (-1)^{p^2} = -1).
    # Wait, k=p^2 -> (-1)^{p^2} = -1. So S_{p^2} = S_{p^2-1} - 1/p^2.
    
    # Let's compute S_{p^2-1} mod p. But S is a sum of fractions.
    # The p-adic valuation of S_{p^2-1}:
    # It contains terms 1/k. If k is a multiple of p, it has negative valuation!
    # So v_p(S_{p^2-1}) is negative.
    
    # Actually, S_{p^2-1} = \sum_{j=1}^{p-1} \sum_{i=0}^{p-1} \frac{(-1)^{i p + j}}{i p + j} + \sum_{m=1}^{p-1} \frac{(-1)^{m p}}{m p}
    # For p=1093, we just need to compute this sum p-adically to a few digits.
    pass

def padic_val_of_S(p):
    # compute sum_{k=1}^{p^2-1} (-1)^k / k in Q_p
    # S = A / B
    # return v_p(A) - v_p(B)
    val = 0
    # Actually we can just compute it exactly using Python fractions for small p
    import fractions
    s = fractions.Fraction(0)
    for k in range(1, p**2):
        s += fractions.Fraction((-1)**k, k)
    
    # v_p(s)
    num, den = s.numerator, s.denominator
    def vp(n):
        c = 0
        while n > 0 and n % p == 0:
            c += 1
            n //= p
        return c
    return vp(num) - vp(den)

for p in [3, 5, 7, 11]:
    print(f"p={p}, v_p(S_{p^2-1}) = {padic_val_of_S(p)}")

