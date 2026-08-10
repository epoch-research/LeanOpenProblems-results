import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

def main():
    primes = [p for p in range(3, 2000) if is_prime(p)]
    # We want to check for p = 3, and q >= 13, so r in range(252) coprime to 252 and r >= 13 (or r in [11] since 11 is handled)
    # Actually, we can check all r coprime to 252
    coprimes = [r for r in range(252) if math.gcd(r, 252) == 1]
    
    print(f"Total coprimes: {len(coprimes)}")
    for r in coprimes:
        if r in [1, 5, 11]:
            continue
        found = False
        for M in [p for p in primes if p != 3]:
            # Check if there are no solutions to r^f - 3^e = 2 mod M
            # with e >= 3 and f >= 2
            # Period of 3 mod M:
            seen3 = {}
            ev = 3
            while True:
                val = pow(3, ev, M)
                if val in seen3:
                    start3 = seen3[val]
                    period3 = ev - seen3[val]
                    break
                seen3[val] = ev
                ev += 1
            # Period of r mod M:
            seen_r = {}
            fv = 2
            while True:
                val = pow(r, fv, M)
                if val in seen_r:
                    start_r = seen_r[val]
                    period_r = fv - seen_r[val]
                    break
                seen_r[val] = fv
                fv += 1
            
            has_sol = False
            for ev_val in range(3, start3 + period3):
                for fv_val in range(2, start_r + period_r):
                    if (pow(r, fv_val, M) - pow(3, ev_val, M) - 2) % M == 0:
                        has_sol = True
                        break
                if has_sol:
                    break
            if not has_sol:
                print(f"r = {r}: ruled out by M = {M}")
                found = True
                break
        if not found:
            print(f"r = {r}: NO MODULUS FOUND!")

if __name__ == "__main__":
    main()
