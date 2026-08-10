import math

def f(x):
    return (math.floor(4*x + 2) + math.floor(9*x + 4) 
            - math.floor(8*x + 4) - math.floor(2*x + 1) - math.floor(3*x + 1))

# Check f(x) for x in [0, 1) at all multiples of denominators 9, 8, 4, 3, 2
points = set()
for d in [9, 8, 4, 3, 2]:
    for i in range(2 * d + 1):
        points.add(i / d)

points = sorted(list(points))
all_nonneg = True
for x in points:
    # check slightly to the right of each point
    mid = x + 1e-9
    val = f(mid)
    if val < 0:
        all_nonneg = False
        print(f"Failed at x={mid}: f(x) = {val}")

print(f"All non-negative for odd n: {all_nonneg}")
