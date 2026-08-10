from sympy import binomial

def A108625(n, k):
    return sum(binomial(n, i)**2 * binomial(n + k - i, k - i) for i in range(k + 1))

# Let's print values for n=3, k=3, 4, 5, 6, 7, 8
vals = [A108625(3, k) for k in range(3, 9)]
print("Values:", vals)
diff1 = [vals[i+1] - vals[i] for i in range(len(vals)-1)]
print("1st diff:", diff1)
diff2 = [diff1[i+1] - diff1[i] for i in range(len(diff1)-1)]
print("2nd diff:", diff2)
diff3 = [diff2[i+1] - diff2[i] for i in range(len(diff2)-1)]
print("3rd diff:", diff3)
