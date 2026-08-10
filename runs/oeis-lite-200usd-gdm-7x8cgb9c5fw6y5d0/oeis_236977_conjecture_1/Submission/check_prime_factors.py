import math

def main():
    limit = 2000005
    is_prime = [True] * limit
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[i]:
            for j in range(i*i, limit, i):
                is_prime[j] = False
                
    # Smallest prime factor
    spf = list(range(limit))
    for i in range(2, int(math.isqrt(limit)) + 1):
        if spf[i] == i:
            for j in range(i*i, limit, i):
                if spf[j] == j:
                    spf[j] = i
                    
    def is_uncovered(n):
        if n % 6 == 3: return False
        if n % 10 == 0: return False
        if n % 6 == 0: return False
        return True

    uncovered_list = [n for n in range(9, 2000000 + 1) if is_uncovered(n)]
    
    with open("/workspace/leanproject/Submission/witnesses.hex", "r") as f:
        hex_str = f.read().strip()
        
    witnesses = [int(hex_str[i:i+4], 16) for i in range(0, len(hex_str), 4)]
    
    large_prime_factors = []
    for n, k in zip(uncovered_list, witnesses):
        # find prime factors of k and n-k
        for x in [k, n - k]:
            temp = x
            while temp > 1:
                p = spf[temp]
                if p > 1409:
                    large_prime_factors.append((n, k, x, p))
                    break
                while temp % p == 0:
                    temp //= p
            if len(large_prime_factors) >= 10:
                break
        if len(large_prime_factors) >= 10:
            break
            
    print(f"Numbers with prime factor > 1409: {len(large_prime_factors)}")
    for item in large_prime_factors[:10]:
        print(f"n={item[0]}, k={item[1]}, term={item[2]}, prime_factor={item[3]}")

if __name__ == "__main__":
    main()
