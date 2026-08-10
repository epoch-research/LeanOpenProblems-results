def main():
    limit = 2000005
    phi = [euler_phi(i) for i in range(limit)]
    primes_set = set(primes(limit))
    squares_set = {i*i for i in range(250000)}
    
    def is_uncovered(n):
        if n % 6 == 3: return False
        if n % 10 == 0: return False
        if n % 6 == 0: return False
        return True

    uncovered_count = 0
    no_prime_witness = []
    
    for n in range(9, 2000000 + 1):
        if not is_uncovered(n):
            continue
        uncovered_count += 1
        
        found = False
        for k in range(1, min((n - 1) // 2, 7000) + 1):
            if (n - k) in primes_set:
                if (phi[k] * phi[n - k]) in squares_set:
                    found = True
                    break
        if not found:
            no_prime_witness.append(n)
            if len(no_prime_witness) < 20:
                print(f"No prime witness for {n}")
                
    print(f"Total uncovered: {uncovered_count}")
    print(f"No prime witness count: {len(no_prime_witness)}")

if __name__ == "__main__":
    main()
