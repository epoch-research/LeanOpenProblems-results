def get_witness(n):
    if n == 1:
        return 1
    queue = [(1 % n, "1")]
    visited = {1 % n}
    while queue:
        rem, path = queue.pop(0)
        if rem == 0:
            return int(path)
        for digit in (0, 1):
            next_rem = (rem * 10 + digit) % n
            if next_rem == 0:
                return int(path + str(digit))
            if next_rem not in visited:
                visited.add(next_rem)
                queue.append((next_rem, path + str(digit)))

print("10001:", get_witness(10001))
print("10003:", get_witness(10003))
print("40959:", get_witness(40959))
