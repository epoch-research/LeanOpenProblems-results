from sage.all import bernoulli, factor

for n in range(7, 1000, 6):
    m = 2*n
    b = bernoulli(m) / m
    num = b.numerator()
    
    rem = 2*n - 1
    cancelled = True
    for p, e in factor(rem):
        if num % (p**e) != 0:
            cancelled = False
            break
            
    if cancelled:
        print(f"WOW! n={n} is completely cancelled!")
