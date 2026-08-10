def solve_conjecture(limit):
    # We want to find if there's any n < limit that cannot be represented as
    # a^2 + 2*b^2 + c^4 + 4*d^4 + c^2 * d^2
    represented = set()
    
    # We can bound a, b, c, d
    # c^4 <= limit => c <= limit^(1/4)
    # 4*d^4 <= limit => d <= (limit/4)^(1/4)
    # 2*b^2 <= limit => b <= (limit/2)^(1/2)
    # a^2 <= limit => a <= limit^(1/2)
    
    max_c = int(limit**0.25) + 1
    max_d = int((limit/4.0)**0.25) + 1
    
    for c in range(max_c):
        c4 = c**4
        for d in range(max_d):
            c2d2 = (c**2) * (d**2)
            d4_4 = 4 * (d**4)
            cd_part = c4 + d4_4 + c2d2
            if cd_part > limit:
                continue
                
            # Now find a^2 + 2*b^2
            max_b = int(((limit - cd_part)/2.0)**0.5) + 1
            for b in range(max_b):
                b_part = cd_part + 2*(b**2)
                if b_part > limit:
                    continue
                max_a = int((limit - b_part)**0.5) + 1
                for a in range(max_a):
                    val = b_part + a**2
                    if val < limit:
                        represented.add(val)
                        
    for n in range(limit):
        if n not in represented:
            print(f"Counterexample found: {n}")
            return n
    print(f"All numbers up to {limit} are represented!")
    return None

solve_conjecture(10000)
