import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

# Prime list
primes = [p for p in range(3, 1000) if is_prime(p)]

def has_sol(q_val, P, is_parity_5):
    # f is odd, so f % 2 = 1. e % 2 = (1 if is_parity_5 else 0)
    # We check if there is any f < P-1, e < P-1
    # with f % 2 == 1 and e % 2 == (1 if is_parity_5 else 0)
    # such that q_val^f - 3^e = 2 mod P
    exp_mod = P - 1
    # Check if 3 % P == 0 or q_val % P == 0
    # if q_val % P == 0: then 0^f - 3^e = 2 mod P => -3^e = 2 mod P, we can still check
    # if 3 % P == 0: then q_val^f - 0 = 2 mod P => q_val^f = 2 mod P
    
    # We can just iterate f in range(exp_mod), e in range(exp_mod)
    # with the parities, and check if (q_val^f - 3^e - 2) % P == 0
    # Wait, the exponent of q_val might have a smaller period, but exp_mod is always a multiple of the period of both 3 and q_val (by Fermat's Little Theorem, if they are coprime, and even if not, we can check 1 to P-1).
    # To be fully general, we check f % 2 == 1, and e % 2 == (1 if is_parity_5 else 0)
    # with f in [1, 3, 5, ..., 2*exp_mod], e in [even/odd ..., 2*exp_mod]
    # Actually, if we just check f in range(2 * exp_mod) and e in range(2 * exp_mod):
    # we can filter by the parity of f and e.
    for f in range(3, 2 * exp_mod + 3):
        if f % 2 != 1: continue
        min_e = 3 if is_parity_5 else 2
        for e in range(min_e, 2 * exp_mod + min_e):
            expected_e_parity = 1 if is_parity_5 else 0
            if e % 2 != expected_e_parity: continue
            
            # Since f and e are actual exponents, we do pow(q_val, f, P) and pow(3, e, P)
            # note that we should handle q_val % P == 0 or 3 % P == 0 correctly.
            # pow handles it correctly.
            val_q = pow(q_val, f, P)
            val_3 = pow(3, e, P)
            if (val_q - val_3 - 2) % P == 0:
                return True
    return False

exceptions = {
    23:  {"is_parity_5": False},
    113: {"is_parity_5": True},
    167: {"is_parity_5": False},
    173: {"is_parity_5": True},
    131: {"is_parity_5": False},
    29:  {"is_parity_5": True},
    83:  {"is_parity_5": False},
    227: {"is_parity_5": False}
}

for r, config in exceptions.items():
    is_parity_5 = config["is_parity_5"]
    print(f"--- Searching for r = {r} (is_parity_5={is_parity_5}) ---")
    
    # We want to find a small C (e.g. 1 to 20) and a list of primes P of length C
    # such that for each k_mod in range(C):
    #   there is a prime P in primes where has_sol((252 * k_mod + r) % P, P, is_parity_5) is False
    #   and (252 * k_mod + r) % P != 0 (so q != P is possible)
    #   Wait, we also need to make sure that q != P contradiction branch works.
    #   In the contradiction branch, if q = P, then we get P % 252 = r.
    #   So we must NOT have P % 252 == r!
    #   Actually, since r >= 23 and we search for small P < 200, P % 252 is just P.
    #   So P != r is sufficient, which is always true since r is not a prime < 200 in some cases, or if r is prime, we just don't pick P = r.
    
    found_C = None
    for C in range(1, 30):
        # Check if we can find a prime P for each k_mod in range(C)
        P_list = []
        possible = True
        for k_mod in range(C):
            q_val_base = 252 * k_mod + r
            # Find a prime P
            found_P = None
            for P in primes:
                if P == r: continue
                # We need q_val_base % P != 0
                if q_val_base % P == 0: continue
                
                # Check if there are no solutions
                if not has_sol(q_val_base % P, P, is_parity_5):
                    found_P = P
                    break
            if found_P is None:
                possible = False
                break
            else:
                P_list.append(found_P)
        if possible:
            found_C = C
            print(f"SUCCESS: C = {C}, P_list = {P_list}")
            break
