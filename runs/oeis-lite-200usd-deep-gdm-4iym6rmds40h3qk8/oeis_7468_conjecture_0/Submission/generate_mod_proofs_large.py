import sympy

def generate_mod_proofs_exhaustive(max_n):
    limit = max_n * (max_n + 1) // 2 * 20 # generous upper bound
    print(f"Sieving primes up to {limit}...")
    is_prime = [True] * limit
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(sympy.integer_nthroot(limit, 2)[0]) + 1):
        if is_prime[i]:
            for j in range(i*i, limit, i):
                is_prime[j] = False
    primes = [i for i, p in enumerate(is_prime) if p]
    print(f"Generated {len(primes)} primes.")

    def qr(m):
        return set((x*x)%m for x in range(m))

    moduli = [3, 4, 5, 7, 8, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
    residues = {m: qr(m) for m in moduli}

    proofs = []
    for n in range(40, max_n + 1):
        start = n*(n-1)//2
        if start + n > len(primes): 
            print(f"Primes exhausted at n = {n}")
            break
        val = sum(primes[start : start + n])
        proved = False
        for m in moduli:
            if (val % m) not in residues[m]:
                proofs.append((n, m))
                proved = True
                break
        if not proved:
            # Let's find any prime modulo that works
            m_cand = 59
            while True:
                # check if prime
                is_p = True
                for d in range(2, int(m_cand**0.5) + 1):
                    if m_cand % d == 0:
                        is_p = False
                        break
                if is_p:
                    if (val % m_cand) not in qr(m_cand):
                        proofs.append((n, m_cand))
                        proved = True
                        break
                m_cand += 1
    return proofs

# Let's see if we can generate up to n = 4000
proofs = generate_mod_proofs_exhaustive(4000)
print(f"Generated proofs for {len(proofs)} values of n.")
# check how many unique moduli
unique_moduli = sorted(list(set(m for n, m in proofs)))
print("Unique moduli used:", unique_moduli)
