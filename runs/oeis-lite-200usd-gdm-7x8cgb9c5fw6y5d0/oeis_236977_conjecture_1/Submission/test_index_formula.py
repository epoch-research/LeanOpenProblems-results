def is_uncovered(x):
    if x % 6 == 3: return False
    if x % 10 == 0: return False
    if x % 6 == 0: return False
    return True

# Build the lookup table for the number of uncovered elements in [0, r - 1]
lookup = [0] * 31
c = 0
for r in range(30):
    lookup[r] = c
    if is_uncovered(r):
        c += 1
lookup[30] = c

# Count uncovered starting from 9
# We want to know the index of n in the list of uncovered numbers starting from 9.
# Let's count how many uncovered numbers there are in [9, n - 1].
def get_index(n):
    # Number of uncovered in [0, n - 1]
    q, r = divmod(n, 30)
    count_n = 18 * q + lookup[r]
    
    # Number of uncovered in [0, 8]
    # 9 is the start, so we subtract the count of [0, 8]
    # let's see: [0, 8] has: 1, 2, 4, 5, 7, 8 (6 elements)
    count_9 = 6
    return count_n - count_9

# Let's test this
uncovered_list = []
for x in range(9, 200000):
    if is_uncovered(x):
        uncovered_list.append(x)

for idx, x in enumerate(uncovered_list):
    calc_idx = get_index(x)
    if calc_idx != idx:
        print(f"Mismatch at {x}: list index {idx}, calculated {calc_idx}")
        exit(1)

print("Success! Formula is 100% correct!")
print(f"Lookup table: {lookup[:30]}")
