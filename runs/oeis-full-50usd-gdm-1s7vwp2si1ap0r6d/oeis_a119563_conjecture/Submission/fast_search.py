import sympy

def find_factor(n, max_p):
    print(f"Searching factor for a({n}) up to {max_p}...")
    for p in sympy.primerange(3, max_p):
        # We want to check if 2^(2^n) + 2^n - 1 == 0 mod p
        # 2^n mod (p-1):
        try:
            pow2_n_mod = pow(2, n, p-1)
            t1 = pow(2, pow2_n_mod, p)
            t2 = pow(2, n, p)
            if (t1 + t2 - 1) % p == 0:
                print(f"a({n}) has prime factor {p}")
                return p
        except ValueError:
            # pow(2, n, p-1) might raise ValueError if p-1 is 0, but p >= 3 so p-1 >= 2
            continue
    print(f"No factor found for a({n}) up to {max_p}")
    return None

find_factor(15, 1000000000)
