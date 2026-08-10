from sage.all import *

for n in [15, 16, 19]:
    found = False
    for p in primes(1000000, 100000000):
        try:
            d = GF(p)(2).multiplicative_order()
        except (ArithmeticError, ValueError):
            continue
        
        pow2_n_mod_d = power_mod(2, n, d)
        t1 = power_mod(2, pow2_n_mod_d, p)
        t2 = power_mod(2, n, p)
        if (t1 + t2 - 1) % p == 0:
            print(f"a({n}) has prime factor {p}", flush=True)
            found = True
            break
    if not found:
        print(f"a({n}) HAS NO FACTOR UNDER 100M", flush=True)

