def F(x):
    import math
    return (math.floor(18*x) + math.floor(4*x) + math.floor(3*x) 
            - math.floor(9*x) - math.floor(8*x) - math.floor(6*x) - math.floor(2*x))

# We only need to check x in [0, 1] at points where the terms change, i.e. multiples of 1/18, 1/8, 1/6, 1/4, 1/3, 1/2
points = set()
for d in [18, 9, 8, 6, 4, 3, 2]:
    for i in range(d + 1):
        points.add(i / d)

points = sorted(list(points))
all_nonneg = True
for x in points[:-1]:
    # check slightly to the right of each point
    mid = x + 1e-9
    val = F(mid)
    if val < 0:
        all_nonneg = False
        print(f"Failed at x={mid}: F(x) = {val}")

print(f"All non-negative for even n: {all_nonneg}")
