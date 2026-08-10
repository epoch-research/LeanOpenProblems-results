import math
import sympy
import heapq

def search():
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151]
    
    # Priority queue stores (g, s, last_prime_index)
    # We start with g=1, s=1
    pq = []
    heapq.heappush(pq, (1, 1, 0))
    
    # To avoid duplicate states and keep queue size manageable, we can limit g.
    # Since we want to search up to 10^16, we can do that.
    LIMIT = 10**16
    
    count = 0
    while pq:
        g, s, idx = heapq.heappop(pq)
        count += 1
        if count % 100000 == 0:
            print(f"Processed {count}, current g = {g}", flush=True)
            
        s_prime = s - g
        if s_prime > 0:
            gc = math.gcd(s_prime, g)
            val = s_prime // gc
            if 1679 % val == 0:
                k = 1679 // val
                b = g // gc
                p = k * b - 1
                if p > 1 and g % p != 0 and sympy.isprime(p):
                    # check gcd(k * a, p) == 1
                    a = s // gc
                    if math.gcd(k * a, p) == 1:
                        print(f"FOUND preimage for 1680!", flush=True)
                        print(f"g = {g}", flush=True)
                        print(f"p = {p}", flush=True)
                        print(f"i = {g * p}", flush=True)
                        return
                        
        for i in range(idx, len(primes)):
            p = primes[i]
            if g * p > LIMIT:
                continue
            
            # Compute sigma(g * p)
            # If g is already divisible by p, we need to adjust
            temp = g
            pe = 1
            while temp % p == 0:
                pe *= p
                temp //= p
            next_s = s * (pe * p * p - 1) // (pe * p - 1)
            next_g = g * p
            
            heapq.heappush(pq, (next_g, next_s, i))

if __name__ == "__main__":
    print("Starting fast smooth search for 1680...")
    search()
