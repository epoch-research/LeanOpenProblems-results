def choose(n, k):
    if n < k: return 0
    if k == 0 or k == n: return 1
    if k > n - k: k = n - k
    ans = 1
    for i in range(1, k + 1):
        ans = ans * (n - i + 1) // i
    return ans

# Precompute lists
max_n = 1000000
w_vals = [choose(w + 2, 2) for w in range(max_n + 1)]
x_vals = []
for x in range(max_n + 1):
    v = choose(x + 3, 4)
    if v > max_n: break
    x_vals.append((x, v))
y_vals = []
for y in range(max_n + 1):
    v = choose(y + 5, 6)
    if v > max_n: break
    y_vals.append((y, v))
z_vals = []
for z in range(max_n + 1):
    v = choose(z + 7, 8)
    if v > max_n: break
    z_vals.append((z, v))

max_w = 0
max_x = 0
max_y = 0
max_z = 0

for n in range(1, max_n + 1):
    found = False
    for z, zv in z_vals:
        if zv > n: break
        for y, yv in y_vals:
            if zv + yv > n: break
            for x, xv in x_vals:
                if zv + yv + xv > n: break
                rem = n - (zv + yv + xv)
                # Check if rem is in w_vals
                # since w_vals[w] = choose(w+2, 2) is strictly increasing, we can do a binary search or math
                # rem = (w+2)(w+1)/2 => 8*rem + 1 = (2w+3)^2.
                import math
                val = 8 * rem + 1
                r = int(math.isqrt(val))
                if r * r == val and r % 2 == 1 and r >= 3:
                    w = (r - 3) // 2
                    max_w = max(max_w, w)
                    max_x = max(max_x, x)
                    max_y = max(max_y, y)
                    max_z = max(max_z, z)
                    found = True
                    break
            if found: break
        if found: break

print(f"Max values for n <= 1000: w={max_w}, x={max_x}, y={max_y}, z={max_z}")

