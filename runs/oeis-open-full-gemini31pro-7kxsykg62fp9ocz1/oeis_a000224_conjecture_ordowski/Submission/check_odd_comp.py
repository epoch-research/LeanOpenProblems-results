from test_bound import A

for n in range(3, 100000, 2):
    # check if composite
    is_comp = False
    for i in range(2, int(n**0.5)+1):
        if n % i == 0:
            is_comp = True
            break
    if not is_comp: continue
    
    a = A(n)
    if a > (n - 1) / 2:
        print(f"FAILED for {n}, A({n}) = {a}, bound = {(n-1)/2}")
