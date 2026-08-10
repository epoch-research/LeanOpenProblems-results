import numpy as np
import math

def solve():
    MAX_N = 100000
    phi = np.arange(MAX_N + 1, dtype=np.int64)
    for i in range(2, MAX_N + 1):
        if phi[i] == i:
            for j in range(i, MAX_N + 1, i):
                phi[j] -= phi[j] // i

    def is_square(x):
        r = int(math.isqrt(x))
        return r * r == x

    uncovered = []
    for n in range(9, MAX_N + 1):
        if n % 6 == 3:
            continue
        if n % 10 == 0:
            continue
        if n % 6 == 0:
            continue
        uncovered.append(n)
        
    print(f"Number of uncovered n up to {MAX_N}: {len(uncovered)}")

    witnesses = []
    for n in uncovered:
        limit = (n - 1) // 2
        found_k = 0
        for k in range(1, limit + 1):
            if is_square(int(phi[k]) * int(phi[n - k])):
                found_k = k
                break
        witnesses.append(found_k)

    # Chunk the match cases into functions of size 1000 each
    chunk_size = 1000
    chunks = []
    for i in range(0, len(uncovered), chunk_size):
        chunks.append((uncovered[i:i+chunk_size], witnesses[i:i+chunk_size]))

    # Primes up to 1414
    limit_primes = 1414
    is_p = [True] * (limit_primes + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(math.isqrt(limit_primes)) + 1):
        if is_p[i]:
            for j in range(i*i, limit_primes + 1, i):
                is_p[j] = False
    primes_1414 = [p for p in range(limit_primes + 1) if is_p[p]]

    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("")
    code.append("set_option maxHeartbeats 0")
    code.append("set_option maxRecDepth 200000")
    code.append("")
    code.append("open Option")
    code.append("")
    code.append(f"def primes_1414 : List UInt32 := {str(primes_1414)}")
    code.append("")
    code.append("def remove_p_fuel (p : UInt32) : Nat → UInt32 → UInt32")
    code.append("  | 0, t => t")
    code.append("  | fuel + 1, t =>")
    code.append("    if t % p == 0 then remove_p_fuel p fuel (t / p) else t")
    code.append("")
    code.append("def totient_list_loop : List UInt32 → UInt32 → UInt32 → UInt32")
    code.append("  | [], temp, acc => if temp > 1 then acc - acc / temp else acc")
    code.append("  | p :: ps, temp, acc =>")
    code.append("    if p * p > temp then")
    code.append("      if temp > 1 then acc - acc / temp else acc")
    code.append("    else if temp % p == 0 then")
    code.append("      let acc' := acc - acc / p")
    code.append("      let temp' := remove_p_fuel p 32 temp")
    code.append("      totient_list_loop ps temp' acc'")
    code.append("    else")
    code.append("      totient_list_loop ps temp acc")
    code.append("")
    code.append("def totient_fast (n : UInt32) : UInt32 :=")
    code.append("  if n == 0 then 0")
    code.append("  else if n == 1 then 1")
    code.append("  else totient_list_loop primes_1414 n n")
    code.append("")
    
    code.append("def sqrt_binary_loop (m : UInt32) : Nat → UInt32 → UInt32 → UInt32")
    code.append("  | 0, _, high => high")
    code.append("  | fuel + 1, low, high =>")
    code.append("    if low > high then high")
    code.append("    else")
    code.append("      let mid := (low + high) / 2")
    code.append("      let sq := mid * mid")
    code.append("      if sq == m then mid")
    code.append("      else if sq > m then")
    code.append("        if mid == 0 then low")
    code.append("        else sqrt_binary_loop m fuel low (mid - 1)")
    code.append("      else")
    code.append("        sqrt_binary_loop m fuel (mid + 1) high")
    code.append("")
    code.append("def sqrt_fast (m : UInt32) : UInt32 :=")
    code.append("  sqrt_binary_loop m 40 0 m")
    code.append("")
    code.append("def is_square_fast (m : UInt32) : Bool :=")
    code.append("  let r := sqrt_fast m")
    code.append("  r * r == m")
    code.append("")

    for idx, (uncovered_chunk, witnesses_chunk) in enumerate(chunks):
        code.append(f"def get_witness_{idx} (n : UInt32) : UInt32 :=")
        code.append("  match n with")
        for n, w in zip(uncovered_chunk, witnesses_chunk):
            code.append(f"  | {n} => {w}")
        code.append("  | _ => 0")
        code.append("")

    code.append("def get_witness (n : UInt32) : UInt32 :=")
    code.append("  if n % 6 == 3 then n / 3")
    code.append("  else if n % 10 == 0 then n / 5")
    code.append("  else if n % 6 == 0 then")
    code.append("    if n % 30 == 0 then n / 10 else n / 6")
    # Binary search over the chunk bounds
    # Since we have len(chunks) chunks:
    # We can write an if-else chain (or a balanced binary search for faster lookup)
    # But since len(chunks) <= 60, a linear if-else chain is extremely fast too!
    for idx, (uncovered_chunk, _) in enumerate(chunks):
        max_n = uncovered_chunk[-1]
        code.append(f"  else if n ≤ {max_n} then get_witness_{idx} n")
    code.append("  else 0")
    code.append("")
    
    code.append("def check_all_loop : Nat → UInt32 → UInt32 → Bool")
    code.append("  | 0, _, _ => true")
    code.append("  | fuel + 1, L, R =>")
    code.append("    if L > R then true")
    code.append("    else if L == R then")
    code.append("      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true")
    code.append("      else")
    code.append("        let k := get_witness L")
    code.append("        if k == 0 then false")
    code.append("        else if k > (L - 1) / 2 then false")
    code.append("        else is_square_fast (totient_fast k * totient_fast (L - k))")
    code.append("    else")
    code.append("      let mid := (L + R) / 2")
    code.append("      check_all_loop fuel L mid && check_all_loop fuel (mid + 1) R")
    code.append("")
    
    code.append(f"theorem test_decide : check_all_loop 25 9 {MAX_N} = true := by")
    code.append("  decide")
    code.append("")
    
    with open("/workspace/leanproject/Submission/TestSpeedFinal.lean", "w") as f:
        f.write("\n".join(code))
    print("TestSpeedFinal.lean written.")

if __name__ == '__main__':
    solve()
