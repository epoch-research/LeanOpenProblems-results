import math
import time

def main():
    print("Sieving...", flush=True)
    limit = 2000005
    phi = list(range(limit))
    is_prime = [True] * limit
    is_prime[0] = is_prime[1] = False
    for i in range(2, limit):
        if phi[i] == i:
            for j in range(i, limit, i):
                phi[j] -= phi[j] // i
                if j > i:
                    is_prime[j] = False
    print("Sieve done.", flush=True)

    print("Precomputing squares...", flush=True)
    squares_set = {i*i for i in range(200000)}
    print("Precomputing squares done.", flush=True)

    def is_square(x):
        return x in squares_set

    def is_uncovered(n):
        if n % 6 == 3: return False
        if n % 10 == 0: return False
        if n % 6 == 0: return False
        return True

    print("Searching witnesses...", flush=True)
    start_time = time.time()
    
    witnesses = []
    max_k = 0
    prime_witness_count = 0
    
    # We will search n from 9 to 2000000
    for n in range(9, 2000000 + 1):
        if not is_uncovered(n):
            continue
            
        # Search for k
        limit_k = min((n - 1) // 2, 7000)
        found_k = None
        
        # To make totient(n-k) fast, we prefer k where n-k is prime.
        # We can search k from 1 upwards.
        for k in range(1, limit_k + 1):
            if is_prime[n - k]:
                if is_square(phi[k] * phi[n - k]):
                    found_k = k
                    prime_witness_count += 1
                    break
                    
        if found_k is None:
            # Fallback to any k
            for k in range(1, limit_k + 1):
                if is_square(phi[k] * phi[n - k]):
                    found_k = k
                    break
                    
        if found_k is None:
            print(f"ERROR: No witness found for {n}!")
            return
            
        witnesses.append(found_k)
        if found_k > max_k:
            max_k = found_k
            
        if len(witnesses) % 100000 == 0:
            print(f"Processed {len(witnesses)} uncovered numbers... Max k so far: {max_k}", flush=True)
            
    end_time = time.time()
    print(f"Finished in {end_time - start_time:.2f} seconds.")
    print(f"Total witnesses: {len(witnesses)}")
    print(f"Max witness k: {max_k}")
    print(f"Prime witness fraction: {prime_witness_count / len(witnesses):.4f}")

if __name__ == "__main__":
    main()
