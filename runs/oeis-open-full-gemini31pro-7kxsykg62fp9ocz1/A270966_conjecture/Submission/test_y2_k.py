import math

gp = []
for z in range(-1000, 1000):
    k = z * (3 * z + 1) // 2
    if k >= 0:
        gp.append(k)
gp.sort()

# check if every m up to 1000 can be y^2 + k with y >= 1
fails = []
for m in range(1000):
    found = False
    for y in range(1, int(math.sqrt(m)) + 1):
        if (m - y*y) in gp:
            found = True
            break
    if not found:
        fails.append(m)

print("Fails:", fails)
