from sympy import Rational, primefactors, mobius

current_sum = Rational(0)
for k in range(1, 100):
    mu = mobius(k)
    # Check if k is squarefree and mu(k) == 1
    # Since mu(k) is 1 or -1 or 0, k is squarefree and mu(k) == 1 iff mu(k) == 1
    if mu == 1:
        current_sum += Rational(1, k)
    A = current_sum.p
    factors = primefactors(A)
    large_factors = [p for p in factors if p > k]
    print(f"k = {k}: sum = {current_sum}, A_k = {A}, large prime factors = {large_factors}")
