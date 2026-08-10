import time

def main():
    print("Sieving using Sage...", flush=True)
    limit = 2000005
    
    # Use list comprehensions in Sage, which are extremely fast
    phi = [euler_phi(i) for i in range(limit)]
    is_prime_list = [is_prime(i) for i in range(limit)]
    primes_set = {i for i, p in enumerate(is_prime_list) if p}
    
    print("Sieve done. Precomputing squares...", flush=True)
    squares_set = {i*i for i in range(250000)}
    print("Precomputing done. Searching...", flush=True)
    
    def is_square(x):
        return x in squares_set

    def is_uncovered(n):
        if n % 6 == 3: return False
        if n % 10 == 0: return False
        if n % 6 == 0: return False
        return True

    start_time = time.time()
    witnesses = []
    max_k = 0
    prime_witness_count = 0
    
    # We search n from 9 to 2000000
    for n in range(9, 2000000 + 1):
        if not is_uncovered(n):
            continue
            
        limit_k = min((n - 1) // 2, 7000)
        found_k = None
        
        # We just search for the first working k
        for k in range(1, limit_k + 1):
            if is_square(phi[k] * phi[n - k]):
                found_k = k
                if (n - k) in primes_set:
                    prime_witness_count += 1
                break
                    
        if found_k is None:
            print(f"ERROR: No witness found for {n}!")
            return
            
        witnesses.append(found_k)
        if found_k > max_k:
            max_k = found_k
            
        if len(witnesses) % 200000 == 0:
            print(f"Processed {len(witnesses)} uncovered... Max k so far: {max_k}", flush=True)
            
    end_time = time.time()
    print(f"Finished in {end_time - start_time:.2f} seconds.")
    print(f"Total witnesses: {len(witnesses)}")
    print(f"Max witness k: {max_k}")
    print(f"Prime witness fraction: {float(prime_witness_count) / len(witnesses):.4f}")
    
    # Now write the hex string
    hex_str = "".join(f"{w:04x}" for w in witnesses)
    with open("/workspace/leanproject/Submission/witnesses.hex", "w") as f:
        f.write(hex_str)
    print("witnesses.hex written.")

if __name__ == "__main__":
    main()
