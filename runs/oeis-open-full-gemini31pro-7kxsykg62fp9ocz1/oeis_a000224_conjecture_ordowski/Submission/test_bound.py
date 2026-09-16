def A_pk(p, k):
    if k == 0: return 1
    if p == 2:
        if k == 1: return 2
        if k == 2: return 2
        return 2**(k-3) + A_pk(2, k-2) # wait, what is the exact formula for A(2^k)?
    else:
        if k == 1: return (p+1)//2
        return (p**k - p**(k-1))//2 + A_pk(p, k-2)

def A(n):
    if n == 1: return 1
    res = 1
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            k = 0
            while n % i == 0:
                k += 1
                n //= i
            res *= A_pk(i, k)
    if n > 1:
        res *= A_pk(n, 1)
    return res

for n in range(4, 1000):
    is_comp = False
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_comp = True
            break
    if not is_comp: continue
    
    a = A(n)
    # Check if a*(a-1) divides n^2-1
    if a > 1 and (n*n-1) % (a*(a-1)) == 0:
        print(f"Counterexample! {n}")
    
    if a > (5*n+4)/12:
        print(f"Failed bound for {n}: A({n}) = {a}, bound = {(5*n+4)/12}")
