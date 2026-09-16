P = 1093**2
M = 1194648
F = 0
fact = 1
for k in range(1, M + 1):
    sign = 1 if k % 2 == 0 else -1
    F = (k * F + sign * fact) % P
    fact = (fact * k) % P

print(F, fact)
