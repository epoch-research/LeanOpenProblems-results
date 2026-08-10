def main():
    import math

    def totient(n):
        t = n
        p = 2
        temp = n
        while p * p <= temp:
            if temp % p == 0:
                while temp % p == 0:
                    temp //= p
                t -= t // p
            if p == 2:
                p = 3
            else:
                p += 2
        if temp > 1:
            t -= t // temp
        return t

    def is_square(x):
        r = int(math.isqrt(x))
        return r * r == x

    MAX_N = 10000
    uncovered = []
    for n in range(9, MAX_N + 1):
        if n % 3 == 0 or n % 10 == 0:
            continue
        uncovered.append(n)

    witnesses = []
    for n in uncovered:
        limit_k = (n - 1) // 2
        found_k = 0
        for k in range(1, limit_k + 1):
            if is_square(totient(k) * totient(n - k)):
                found_k = k
                break
        witnesses.append(found_k)

    # Encode witnesses as hex characters
    hex_str = ""
    for w in witnesses:
        hex_str += f"{w:04x}"

    code = []
    code.append("import FormalConjectures.Util.ProblemImports")
    code.append("set_option maxRecDepth 200000")
    code.append("set_option maxHeartbeats 0")
    code.append("")
    code.append("open Nat")
    code.append("")
    
    # Primes list in UInt32
    limit_primes = 1414
    is_p = [True] * (limit_primes + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(math.isqrt(limit_primes)) + 1):
        if is_p[i]:
            for j in range(i*i, limit_primes + 1, i):
                is_p[j] = False
    primes_1414 = [p for p in range(limit_primes + 1) if is_p[p]]
    primes_str = ", ".join(f"{p}" for p in primes_1414)
    code.append(f"def primes_1414 : List UInt32 := [{primes_str}]")
    code.append("")

    # totient_fast with List recursion in UInt32
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

    # sqrt_fast and is_square_fast with UInt32
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

    # Pack into 2 variables of size 5000
    chunk_size = 5000
    chunks = [witnesses[i:i+chunk_size] for i in range(0, len(witnesses), chunk_size)]
    for idx, chunk in enumerate(chunks):
        val = 0
        for i, w in enumerate(chunk):
            val |= (int(w) & 0xFFFF) << (16 * i)
        code.append(f"def huge_nat_{idx} : Nat := {hex(val)}")
        code.append("")

    code.append("def get_witness_from_tree (chunk_idx : Nat) (offset : Nat) : UInt32 :=")
    if len(chunks) == 1:
        code.append("  (shiftRight huge_nat_0 (16 * offset) % 65536).toUInt32")
    else:
        code.append("  if chunk_idx == 0 then (shiftRight huge_nat_0 (16 * offset) % 65536).toUInt32")
        code.append("  else (shiftRight huge_nat_1 (16 * offset) % 65536).toUInt32")
    code.append("")

    code.append("def get_uncovered_index (n : Nat) : Nat :=")
    code.append("  n - (n / 3 + n / 10 - n / 30) - 6")
    code.append("")
    code.append("def get_witness_final (n : Nat) : UInt32 :=")
    code.append("  if n % 6 == 3 then (n / 3).toUInt32")
    code.append("  else if n % 10 == 0 then (n / 5).toUInt32")
    code.append("  else if n % 6 == 0 then")
    code.append("    if n % 30 == 0 then (n / 10).toUInt32 else (n / 6).toUInt32")
    code.append("  else")
    code.append("    let idx := get_uncovered_index n - 1")
    code.append("    get_witness_from_tree (idx / 5000) (idx % 5000)")
    code.append("")

    # check_all_loop
    code.append("def check_all_loop : Nat → Nat → Nat → Bool")
    code.append("  | 0, _, _ => true")
    code.append("  | fuel + 1, L, R =>")
    code.append("    if L > R then true")
    code.append("    else if L == R then")
    code.append("      if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true")
    code.append("      else")
    code.append("        let k := get_witness_final L")
    code.append("        if k == 0 then false")
    code.append("        else if k.toNat > (L - 1) / 2 then false")
    code.append("        else")
    code.append("          let tot1 := totient_fast k")
    code.append("          let tot2 := totient_fast (L.toUInt32 - k)")
    code.append("          is_square_fast (tot1 * tot2)")
    code.append("    else")
    code.append("      let mid := (L + R) / 2")
    code.append("      check_all_loop fuel L mid && check_all_loop fuel (mid + 1) R")
    code.append("")

    code.append("theorem test_decide : check_all_loop 25 9 10000 = true := by")
    code.append("  decide")
    code.append("")

    with open("/workspace/leanproject/Submission/TestSpeed10k_uint32.lean", "w") as f:
        f.write("\n".join(code))
    print("Generated TestSpeed10k_uint32.lean!")

if __name__ == "__main__":
    main()
