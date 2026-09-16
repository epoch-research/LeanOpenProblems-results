p = 1093
s = 0
for k in range(1, p**2):
    if k % p != 0:
        s = (s + (-1)**k * pow(k, p-2, p)) % p
    else:
        # p | k
        pass
print("Sum without p|k :", s)
