import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

def has_sol(val, M):
    # e >= 3 and f >= 2
    # period of 3 mod M
    seen3 = {}
    ev = 3
    while True:
        val3 = pow(3, ev, M)
        if val3 in seen3:
            start3 = seen3[val3]
            period3 = ev - seen3[val3]
            break
        seen3[val3] = ev
        ev += 1
    # period of val mod M
    seen_val = {}
    fv = 2
    while True:
        val_v = pow(val, fv, M)
        if val_v in seen_val:
            start_val = seen_val[val_v]
            period_val = fv - seen_val[val_v]
            break
        seen_val[val_v] = fv
        fv += 1
    
    for ev_val in range(3, start3 + period3):
        for fv_val in range(2, start_val + period_val):
            if (pow(val, fv_val, M) - pow(3, ev_val, M) - 2) % M == 0:
                return True
    return False

def main():
    primes = [p for p in range(3, 2000) if is_prime(p)]
    coprimes = [r for r in range(252) if math.gcd(r, 252) == 1]
    
    for r in coprimes:
        if r in [1, 5, 11]:
            continue
        found_M = None
        # Check M = 9 first
        if not has_sol(r % 9, 9):
            found_M = 9
        else:
            for M in [p for p in primes if p != 3]:
                if not has_sol(r % M, M):
                    found_M = M
                    break
        print(f"r = {r}: ruled out by M = {found_M}")

if __name__ == "__main__":
    main()
