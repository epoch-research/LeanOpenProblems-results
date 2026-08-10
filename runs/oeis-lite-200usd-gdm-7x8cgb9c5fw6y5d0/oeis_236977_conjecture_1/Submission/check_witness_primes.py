import math

def main():
    limit = 2000005
    is_prime = [True] * limit
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[i]:
            for j in range(i*i, limit, i):
                is_prime[j] = False
                
    def is_uncovered(n):
        if n % 6 == 3: return False
        if n % 10 == 0: return False
        if n % 6 == 0: return False
        return True

    uncovered_list = [n for n in range(9, 2000000 + 1) if is_uncovered(n)]
    
    with open("/workspace/leanproject/Submission/witnesses.hex", "r") as f:
        hex_str = f.read().strip()
        
    witnesses = [int(hex_str[i:i+4], 16) for i in range(0, len(hex_str), 4)]
    
    composite_count = 0
    prime_count = 0
    for n, k in zip(uncovered_list, witnesses):
        if is_prime[n - k]:
            prime_count += 1
        else:
            composite_count += 1
            if composite_count < 20:
                print(f"Composite n-k at n={n}, k={k}, n-k={n-k}")
                
    print(f"Total uncovered: {len(witnesses)}")
    print(f"Prime n-k: {prime_count}")
    print(f"Composite n-k: {composite_count}")

if __name__ == "__main__":
    main()
