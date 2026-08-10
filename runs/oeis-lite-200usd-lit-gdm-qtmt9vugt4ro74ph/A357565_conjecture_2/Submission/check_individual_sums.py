import math

def choose(n, k):
    return math.comb(n, k)

def s2(n):
    return sum(choose(n+k-1, k)**2 for k in range(n+1))

def s3(n):
    return sum(choose(n+k-1, k)**3 for k in range(n+1))

for n in range(1, 11):
    print(f"n={n}: s2={s2(n)}, s3={s3(n)}")
