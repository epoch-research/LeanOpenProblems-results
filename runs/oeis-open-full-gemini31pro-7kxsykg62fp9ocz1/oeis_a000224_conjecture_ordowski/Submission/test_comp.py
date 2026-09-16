for n in range(3, 1000000, 2):
    # is prime?
    is_prime = True
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_prime = False
            break
    if is_prime: continue
    
    # calc A(n)
    a = 1
    temp = n
    for i in range(2, int(n**0.5)+1):
        if temp % i == 0:
            k = 0
            while temp % i == 0:
                k += 1
                temp //= i
            # A_pk for odd p
            val = (i**k - i**(k-1))//2
            if k >= 2:
                # need full recursive
                def A_pk(p, k):
                    if k == 0: return 1
                    if k == 1: return (p+1)//2
                    return (p**k - p**(k-1))//2 + A_pk(p, k-2)
                val = A_pk(i, k)
            else:
                val = (i+1)//2
            a *= val
    if temp > 1:
        a *= (temp+1)//2
        
    M = a * (a - 1)
    if M > 0 and (n*n - 1) % M == 0:
        print(f"Match: {n}")
