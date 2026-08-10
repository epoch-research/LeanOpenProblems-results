from collections import deque
import multiprocessing
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

def generate_range(idx):
    low = 10000 + idx * 1000
    high = 10000 + (idx + 1) * 1000
    lines = []
    lines.append(f"def witness_large_{idx} : Nat → Nat\n")
    for n in range(low, high):
        if n % 10 in (1, 3, 7, 9) and n not in exceptions:
            w = get_witness(n)
            lines.append(f"  | {n} => {w}\n")
    lines.append("  | _ => 1\n\n")
    return idx, "".join(lines)

if __name__ == "__main__":
    start_time = time.time()
    print("Starting parallel generation of 90 functions...")
    pool = multiprocessing.Pool(processes=32) # Use 32 cores!
    results = pool.map(generate_range, range(90))
    results.sort() # Ensure we write them in order
    
    with open("/workspace/leanproject/Submission/WitnessLargeFunctions.lean", "w") as f:
        f.write("import FormalConjectures.Util.ProblemImports\n\n")
        for idx, content in results:
            f.write(content)
            
    print(f"Finished in {time.time() - start_time:.2f} seconds.")
