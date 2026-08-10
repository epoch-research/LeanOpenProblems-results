from collections import deque
import time

def get_witness(n):
    if n == 1: return 1
    queue = deque([(1 % n, 1)])
    visited = [False] * n
    visited[1 % n] = True
    while queue:
        rem, val = queue.popleft()
        if rem == 0:
            return val
        for digit in (0, 1):
            next_rem = (rem * 10 + digit) % n
            if not visited[next_rem]:
                visited[next_rem] = True
                queue.append((next_rem, val * 10 + digit))

exceptions = {76923, 10989, 29997, 32967, 69993, 89991, 40959, 81918, 41841, 83682, 72927, 88911, 98901}

print("Starting witness generation...")
start_time = time.time()

# Generate the 9 lookup functions
with open("/workspace/leanproject/Submission/WitnessLargeFunctions.lean", "w") as f:
    for idx in range(9):
        low = (idx + 1) * 10000
        high = (idx + 2) * 10000
        print(f"Generating for range [{low}, {high})...")
        f.write(f"def witness_large_{idx} : Nat → Nat\n")
        count = 0
        for n in range(low, high):
            if n % 10 in (1, 3, 7, 9) and n not in exceptions:
                w = get_witness(n)
                f.write(f"  | {n} => {w}\n")
                count += 1
        f.write("  | _ => 1\n\n")

print(f"Finished in {time.time() - start_time:.2f} seconds.")
