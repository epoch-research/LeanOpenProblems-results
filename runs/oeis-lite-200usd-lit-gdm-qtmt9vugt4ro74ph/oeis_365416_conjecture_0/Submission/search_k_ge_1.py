import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

def has_sol(val, M):
    for f in range(2, 50):
        for e in range(3, 50):
            if (pow(val, f, M) - pow(3, e, M) - 2) % M == 0:
                return True
    return False

def main():
    exceptions = [29, 83, 149, 227]
    
    # We can search M up to 1000
    for r in exceptions:
        found_M = None
        for M in range(3, 1000):
            if math.gcd(252, M) > 1: # wait, composite moduli can share factors with 252!
                pass
            # For each k >= 1 such that q = 252*k + r is coprime to M:
            # We only need to check val = (252*k + r) % M for k in range(1, M+1)
            # such that gcd(252*k + r, M) == 1 (or we can just check if M is prime, then val != 0)
            all_ruled = True
            for k in range(1, M + 1):
                val = (252 * k + r) % M
                # If val is not coprime to M, and q is prime, can q % M = val?
                # Only if q <= M. But q >= 252 + r >= 281.
                # So if M < 281, then gcd(q, M) must be 1.
                # So we can skip any val which is not coprime to M!
                if math.gcd(val, M) > 1:
                    continue
                if has_sol(val, M):
                    all_ruled = False
                    break
            if all_ruled:
                found_M = M
                break
        print(f"r = {r}: ruled out by M = {found_M}")

if __name__ == "__main__":
    main()
